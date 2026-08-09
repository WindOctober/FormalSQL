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

Require Import ZArith Bool Lia.

Open Scope Z_scope.

Definition z_le_bool x y :=
  match Z.compare x y with Gt => false | _ => true end.

Lemma z_le_bool_true_iff :
  forall x y, z_le_bool x y = true <-> x <= y.
Proof.
intros x y; unfold z_le_bool.
destruct (Z.compare_spec x y); split; intro Hb; try reflexivity;
  try discriminate; lia.
Qed.

Lemma z_le_bool_false_iff :
  forall x y, z_le_bool x y = false <-> y < x.
Proof.
intros x y; unfold z_le_bool.
destruct (Z.compare_spec x y); split; intro Hb; try reflexivity;
  try discriminate; lia.
Qed.

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

Lemma valid_ymd_true_iff :
  forall y m d,
    valid_ymd y m d = true <->
    1 <= m <= 12 /\ 1 <= d <= days_in_month y m.
Proof.
intros y m d; unfold valid_ymd.
repeat rewrite andb_true_iff.
repeat rewrite z_le_bool_true_iff.
reflexivity.
Qed.

Definition days_from_civil y m d :=
  let y := if z_le_bool m 2 then y - 1 else y in
  let era := Z.div y 400 in
  let yoe := y - era * 400 in
  let mp := if z_le_bool 3 m then m - 3 else m + 9 in
  let doy := Z.div (153 * mp + 2) 5 + d - 1 in
  let doe := yoe * 365 + Z.div yoe 4 - Z.div yoe 100 + doy in
  era * 146097 + doe - 719468.

(**
  PostgreSQL stores DATE relative to 2000-01-01 and TIMESTAMP in microseconds
  relative to that same epoch.  FormalSQL uses the Unix epoch instead, so the
  bounds below are the PostgreSQL finite ranges translated to this carrier.
  Upper bounds are exclusive, as in PostgreSQL's IS_VALID_DATE and
  IS_VALID_TIMESTAMP checks.  Because this carrier is relative to the Unix
  epoch rather than PostgreSQL's epoch, the special +/-infinity values use the
  immediately adjacent integers instead of PostgreSQL's physical int32/int64
  sentinels.  This preserves their observable ordering without conflating a
  finite date or timestamp with a special value.
*)
Definition postgres_date_min : Z := -2440588.
Definition postgres_date_end : Z := 2145042906.
Definition postgres_date_neg_infinity : Z := postgres_date_min - 1.
Definition postgres_date_pos_infinity : Z := postgres_date_end.

Definition date_in_range_bool (date : Z) : bool :=
  (postgres_date_min <=? date) && (date <? postgres_date_end).

Lemma date_in_range_bool_true_iff :
  forall date,
    date_in_range_bool date = true <->
    postgres_date_min <= date < postgres_date_end.
Proof.
intro date; unfold date_in_range_bool.
rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

Definition date_is_neg_infinity_bool (date : Z) : bool :=
  date =? postgres_date_neg_infinity.

Definition date_is_pos_infinity_bool (date : Z) : bool :=
  date =? postgres_date_pos_infinity.

Definition date_is_infinity_bool (date : Z) : bool :=
  date_is_neg_infinity_bool date || date_is_pos_infinity_bool date.

Lemma date_is_infinity_bool_true_iff :
  forall date,
    date_is_infinity_bool date = true <->
    date = postgres_date_neg_infinity \/
    date = postgres_date_pos_infinity.
Proof.
intro date; unfold date_is_infinity_bool, date_is_neg_infinity_bool,
  date_is_pos_infinity_bool.
rewrite orb_true_iff, Z.eqb_eq, Z.eqb_eq; reflexivity.
Qed.

Definition date_value_valid_bool (date : Z) : bool :=
  date_in_range_bool date || date_is_infinity_bool date.

Lemma date_value_valid_bool_true_iff :
  forall date,
    date_value_valid_bool date = true <->
    postgres_date_min <= date < postgres_date_end \/
    date = postgres_date_neg_infinity \/
    date = postgres_date_pos_infinity.
Proof.
intro date; unfold date_value_valid_bool.
rewrite orb_true_iff, date_in_range_bool_true_iff,
  date_is_infinity_bool_true_iff; reflexivity.
Qed.

Definition date_checked (date : Z) : option Z :=
  if date_in_range_bool date then Some date else None.

Definition date_from_ymd y m d :=
  if valid_ymd y m d then date_checked (days_from_civil y m d) else None.

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

(** PostgreSQL [extract(year from date)] uses the civil year and has no year
    zero: astronomical year 0 is reported as 1 BC, i.e. -1. *)
Definition date_extract_year date :=
  let '(year, _, _) := civil_from_days date in
  if 0 <? year then year else year - 1.

(** PostgreSQL returns the civil month unchanged for every finite DATE.  The
    internal astronomical year used by [civil_from_days] affects YEAR around
    1 BC, but not the 1..12 month component. *)
Definition date_extract_month date :=
  let '(_, month, _) := civil_from_days date in month.

Theorem date_extract_month_days_from_civil :
  forall y m d,
    valid_ymd y m d = true ->
    date_extract_month (days_from_civil y m d) = m.
Proof.
intros y m d Hvalid.
assert (Hle : forall x z, z_le_bool x z = true <-> x <= z)
  by exact z_le_bool_true_iff.
assert (Hnle : forall x z, z_le_bool x z = false <-> z < x)
  by exact z_le_bool_false_iff.
apply valid_ymd_true_iff in Hvalid.
destruct Hvalid as [[Hmlo Hmhi] [Hdlo Hdhi]].

assert (Hregular_year_of_era :
  forall yoe doy,
    0 <= yoe < 400 ->
    0 <= doy < 365 ->
    let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy in
    (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 = yoe).
{
  intros yoe doy Hyoe Hdoy; cbn.
  set (doe := yoe * 365 + yoe / 4 - yoe / 100 + doy).
  pose proof (Z.mod_pos_bound yoe 4 ltac:(lia)) as H4.
  pose proof (Z.mod_pos_bound yoe 100 ltac:(lia)) as H100.
  rewrite Z.mod_eq in H4, H100 by lia.
  assert (Hdoe : 0 <= doe < 146096) by (subst doe; lia).
  assert (H146096 : doe / 146096 = 0) by
    (apply Z.div_small; exact Hdoe).
  pose proof (Z.mod_pos_bound doe 1460 ltac:(lia)) as H1460.
  pose proof (Z.mod_pos_bound doe 36524 ltac:(lia)) as H36524.
  rewrite Z.mod_eq in H1460, H36524 by lia.
  assert (H36524q : doe / 36524 = yoe / 100) by (subst doe; lia).
  assert (H1460bounds : yoe / 4 <= doe / 1460 <= yoe / 4 + 1) by
    (subst doe; lia).
  assert (H1460inc : doe / 1460 = yoe / 4 + 1 -> 1 <= doy) by
    (subst doe; lia).
  rewrite H146096, H36524q; symmetry.
  apply Z.div_unique_pos with
    (r := doe - doe / 1460 + yoe / 100 - 365 * yoe).
  - subst doe; lia.
  - ring.
}

assert (Hleap_year_of_era :
  forall yoe,
    0 <= yoe < 400 ->
    (yoe + 1) mod 4 = 0 ->
    ((yoe + 1) mod 100 <> 0 \/ (yoe + 1) mod 400 = 0) ->
    let doe := yoe * 365 + yoe / 4 - yoe / 100 + 365 in
    (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 = yoe).
{
  intros yoe Hyoe H4leap Hcentury; cbn.
  set (doe := yoe * 365 + yoe / 4 - yoe / 100 + 365).
  pose proof (Z.mod_pos_bound yoe 4 ltac:(lia)) as H4.
  pose proof (Z.mod_pos_bound yoe 100 ltac:(lia)) as H100.
  pose proof (Z.mod_pos_bound (yoe + 1) 100 ltac:(lia)) as Hnext100.
  pose proof (Z.mod_pos_bound (yoe + 1) 400 ltac:(lia)) as Hnext400.
  pose proof (Z.mod_pos_bound doe 1460 ltac:(lia)) as H1460.
  pose proof (Z.mod_pos_bound doe 36524 ltac:(lia)) as H36524.
  pose proof (Z.mod_pos_bound doe 146096 ltac:(lia)) as H146096.
  rewrite Z.mod_eq in H4, H100, Hnext100, Hnext400,
    H1460, H36524, H146096, H4leap by lia.
  destruct Hcentury as [Hnoncentury | Hfourhundred].
  - rewrite Z.mod_eq in Hnoncentury by lia.
    assert (H1460q : doe / 1460 = yoe / 4 + 1) by (subst doe; lia).
    assert (Hcorrection :
      doe / 36524 - doe / 146096 = yoe / 100) by (subst doe; lia).
    rewrite H1460q; symmetry.
    apply Z.div_unique_pos with (r := 364); [lia | subst doe; lia].
  - rewrite Z.mod_eq in Hfourhundred by lia.
    assert (Hlast : yoe = 399) by lia.
    subst yoe; vm_compute; reflexivity.
}

set (adjusted_year := if z_le_bool m 2 then y - 1 else y).
set (era := adjusted_year / 400).
set (yoe := adjusted_year - era * 400).
set (mp := if z_le_bool 3 m then m - 3 else m + 9).
set (doy := (153 * mp + 2) / 5 + d - 1).
set (doe := yoe * 365 + yoe / 4 - yoe / 100 + doy).

assert (Hcalendar :
  0 <= doy <= 365 /\
  (doy = 365 -> m = 2 /\ d = 29 /\ is_leap_year y = true) /\
  (5 * doy + 2) / 153 = mp /\
  mp + (if z_le_bool mp 9 then 3 else -9) = m).
{
  assert (Hdoydef : doy = (153 * mp + 2) / 5 + d - 1) by
    (unfold doy; reflexivity).
  pose proof (Z.mod_pos_bound (153 * mp + 2) 5 ltac:(lia)) as Hbase.
  pose proof (Z.mod_pos_bound (5 * doy + 2) 153 ltac:(lia)) as Hselected.
  rewrite Z.mod_eq in Hbase, Hselected by lia.
  assert (Hmp_relation :
    (m <= 2 /\ mp = m + 9) \/ (3 <= m /\ mp = m - 3)).
  {
    destruct (z_le_bool 3 m) eqn:Hm3.
    - right; split; [apply Hle; exact Hm3 | unfold mp; reflexivity].
    - left; split; [apply Hnle in Hm3; lia | unfold mp; reflexivity].
  }
  assert (Hmp_bounds : 0 <= mp < 12).
  {
    destruct Hmp_relation as [[Hm2 Hmp_relation] | [Hm3 Hmp_relation]];
      rewrite Hmp_relation; lia.
  }
  assert (Hmonth_decode :
    mp + (if z_le_bool mp 9 then 3 else -9) = m).
  {
    destruct Hmp_relation as [[Hm2 Hmp_relation] | [Hm3 Hmp_relation]];
      destruct (z_le_bool mp 9) eqn:Hmp9;
      [apply Hle in Hmp9 | apply Hnle in Hmp9
      | apply Hle in Hmp9 | apply Hnle in Hmp9]; lia.
  }
  assert (Hcalendar_core :
    0 <= doy <= 365 /\
    (doy = 365 -> m = 2 /\ d = 29 /\ is_leap_year y = true) /\
    (5 * doy + 2) / 153 = mp).
  {
    clear Hmonth_decode Hmp_bounds.
    assert (Hmonths :
      m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/
      m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12) by lia.
    let rec destruct_months H :=
      lazymatch type of H with
      | _ \/ _ =>
          destruct H as [Hm | Hrest];
          [subst m | destruct_months Hrest]
      | _ => subst m
      end in destruct_months Hmonths.
    all: destruct Hmp_relation as [[Hm2 Hmp] | [Hm3 Hmp]]; try lia.
    all: rewrite Hmp in Hdoydef, Hbase |- *.
    all: destruct (is_leap_year y) eqn:Hleap.
    all: cbn [days_in_month] in Hdhi.
    all: try rewrite Hleap in Hdhi.
    all: repeat split; intros; try lia; try assumption.
  }
  destruct Hcalendar_core as [Hdoy_bounds [Hdoy_max Hmp_inverse]].
  exact (conj Hdoy_bounds (conj Hdoy_max (conj Hmp_inverse Hmonth_decode))).
}
destruct Hcalendar as [Hdoy [Hdoy365 [Hmp Hmonth]]].

assert (Hyoe : 0 <= yoe < 400).
{
  unfold yoe, era.
  pose proof (Z.mod_pos_bound adjusted_year 400 ltac:(lia)) as Hmod.
  rewrite Z.mod_eq in Hmod by lia; lia.
}
pose proof (Z.mod_pos_bound yoe 4 ltac:(lia)) as Hyoe4.
pose proof (Z.mod_pos_bound yoe 100 ltac:(lia)) as Hyoe100.
rewrite Z.mod_eq in Hyoe4, Hyoe100 by lia.
assert (Hdoe : 0 <= doe < 146097) by (unfold doe; lia).
assert (Hdays : days_from_civil y m d + 719468 = era * 146097 + doe).
{
  unfold days_from_civil.
  change (era * 146097 + doe - 719468 + 719468 = era * 146097 + doe).
  ring.
}
assert (Hera : (era * 146097 + doe) / 146097 = era).
{
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by exact Hdoe; lia.
}

assert (Hyoe_inverse :
  (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 = yoe).
{
  destruct (Z_lt_ge_dec doy 365) as [Hdoylt | Hdoyge].
  - apply Hregular_year_of_era; lia.
  - assert (Hdoyeq : doy = 365) by lia.
    destruct (Hdoy365 Hdoyeq) as [Hm2 [Hd29 Hleap]].
    assert (Hadjusted : adjusted_year = y - 1).
    { unfold adjusted_year; rewrite Hm2; reflexivity. }
    assert (Hy : y = yoe + 1 + era * 400) by
      (unfold yoe; rewrite Hadjusted; lia).
    unfold is_leap_year in Hleap.
    rewrite andb_true_iff, orb_true_iff in Hleap.
    unfold doe; rewrite Hdoyeq.
    destruct Hleap as [H4 [H100 | H400]].
    + apply Z.eqb_eq in H4.
      apply negb_true_iff, Z.eqb_neq in H100.
      apply Hleap_year_of_era; [exact Hyoe | | left].
      * rewrite Hy in H4.
        replace (yoe + 1 + era * 400) with
          (yoe + 1 + (era * 100) * 4) in H4 by ring.
        rewrite Z.mod_add in H4 by lia; exact H4.
      * rewrite Hy in H100.
        replace (yoe + 1 + era * 400) with
          (yoe + 1 + (era * 4) * 100) in H100 by ring.
        rewrite Z.mod_add in H100 by lia; exact H100.
    + apply Z.eqb_eq in H4, H400.
      apply Hleap_year_of_era; [exact Hyoe | | right].
      * rewrite Hy in H4.
        replace (yoe + 1 + era * 400) with
          (yoe + 1 + (era * 100) * 4) in H4 by ring.
        rewrite Z.mod_add in H4 by lia; exact H4.
      * rewrite Hy in H400.
        rewrite Z.mod_add in H400 by lia; exact H400.
}

unfold date_extract_month, civil_from_days.
cbv beta iota zeta.
rewrite Hdays, Hera.
replace (era * 146097 + doe - era * 146097) with doe by ring.
rewrite Hyoe_inverse.
replace (doe - (365 * yoe + yoe / 4 - yoe / 100)) with doy by
  (unfold doe; ring).
rewrite Hmp, Hmonth.
reflexivity.
Qed.

Lemma date_extract_year_unix_epoch : date_extract_year 0 = 1970.
Proof. reflexivity. Qed.

Lemma date_extract_year_postgres_epoch : date_extract_year 10957 = 2000.
Proof. reflexivity. Qed.

Lemma date_extract_month_unix_epoch : date_extract_month 0 = 1.
Proof. reflexivity. Qed.

Lemma date_extract_month_postgres_epoch : date_extract_month 10957 = 1.
Proof. reflexivity. Qed.

Lemma date_extract_month_april_boundary : date_extract_month 16161 = 4.
Proof. reflexivity. Qed.

Lemma date_extract_month_astronomical_year_zero :
  date_extract_month (-719179) = 12.
Proof. reflexivity. Qed.

Definition date_add_months date months :=
  let '(y, m, d) := civil_from_days date in
  let month_index := y * 12 + (m - 1) + months in
  let y' := Z.div month_index 12 in
  let m' := Z.modulo month_index 12 + 1 in
  days_from_civil y' m' (Z.min d (days_in_month y' m')).

Definition micros_per_second := 1000000.
Definition micros_per_minute := 60 * micros_per_second.
Definition micros_per_hour := 60 * micros_per_minute.
Definition micros_per_day := 24 * micros_per_hour.

Definition postgres_timestamp_min : Z := -210866803200000000.
Definition postgres_timestamp_end : Z := 9224318016000000000.
Definition postgres_timestamp_neg_infinity : Z := postgres_timestamp_min - 1.
Definition postgres_timestamp_pos_infinity : Z := postgres_timestamp_end.

Definition timestamp_in_range_bool (timestamp : Z) : bool :=
  (postgres_timestamp_min <=? timestamp)
  && (timestamp <? postgres_timestamp_end).

Lemma timestamp_in_range_bool_true_iff :
  forall timestamp,
    timestamp_in_range_bool timestamp = true <->
    postgres_timestamp_min <= timestamp < postgres_timestamp_end.
Proof.
intro timestamp; unfold timestamp_in_range_bool.
rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

Definition timestamp_is_neg_infinity_bool (timestamp : Z) : bool :=
  timestamp =? postgres_timestamp_neg_infinity.

Definition timestamp_is_pos_infinity_bool (timestamp : Z) : bool :=
  timestamp =? postgres_timestamp_pos_infinity.

Definition timestamp_is_infinity_bool (timestamp : Z) : bool :=
  timestamp_is_neg_infinity_bool timestamp
  || timestamp_is_pos_infinity_bool timestamp.

Lemma timestamp_is_infinity_bool_true_iff :
  forall timestamp,
    timestamp_is_infinity_bool timestamp = true <->
    timestamp = postgres_timestamp_neg_infinity \/
    timestamp = postgres_timestamp_pos_infinity.
Proof.
intro timestamp; unfold timestamp_is_infinity_bool,
  timestamp_is_neg_infinity_bool, timestamp_is_pos_infinity_bool.
rewrite orb_true_iff, Z.eqb_eq, Z.eqb_eq; reflexivity.
Qed.

Definition timestamp_value_valid_bool (timestamp : Z) : bool :=
  timestamp_in_range_bool timestamp || timestamp_is_infinity_bool timestamp.

Lemma timestamp_value_valid_bool_true_iff :
  forall timestamp,
    timestamp_value_valid_bool timestamp = true <->
    postgres_timestamp_min <= timestamp < postgres_timestamp_end \/
    timestamp = postgres_timestamp_neg_infinity \/
    timestamp = postgres_timestamp_pos_infinity.
Proof.
intro timestamp; unfold timestamp_value_valid_bool.
rewrite orb_true_iff, timestamp_in_range_bool_true_iff,
  timestamp_is_infinity_bool_true_iff; reflexivity.
Qed.

(** PostgreSQL stores finite TIMESTAMP/TIMESTAMPTZ values in microseconds and
    applies the declared precision when a value enters a typed column.  A
    precision [p] therefore admits exactly multiples of [10^(6-p)]
    microseconds.  The two infinity sentinels are independent of precision.

    Keeping this check in the value model is important for quantified database
    states: otherwise a schema such as [timestamp(0)] would admit an abstract
    half-second value that no PostgreSQL instance of that schema can contain. *)
Definition timestamp_precision_valid_bool (precision : Z) : bool :=
  (0 <=? precision) && (precision <=? 6).

Lemma timestamp_precision_valid_bool_true_iff :
  forall precision,
    timestamp_precision_valid_bool precision = true <->
    0 <= precision <= 6.
Proof.
intro precision; unfold timestamp_precision_valid_bool.
rewrite andb_true_iff, Z.leb_le, Z.leb_le; reflexivity.
Qed.

Definition timestamp_fits_precision_bool
    (timestamp precision : Z) : bool :=
  if timestamp_precision_valid_bool precision then
    if timestamp_is_infinity_bool timestamp then true
    else
      timestamp_in_range_bool timestamp
      && (timestamp mod (Z.pow 10 (6 - precision)) =? 0)
  else false.

Definition timestamp_checked (timestamp : Z) : option Z :=
  if timestamp_in_range_bool timestamp then Some timestamp else None.

Definition valid_time h m s micros :=
  andb (andb (z_le_bool 0 h) (z_le_bool h 23))
       (andb (andb (z_le_bool 0 m) (z_le_bool m 59))
             (andb (andb (z_le_bool 0 s) (z_le_bool s 59))
                   (andb (z_le_bool 0 micros) (z_le_bool micros 999999)))).

Lemma valid_time_true_iff :
  forall h m s micros,
    valid_time h m s micros = true <->
    0 <= h <= 23 /\ 0 <= m <= 59 /\
    0 <= s <= 59 /\ 0 <= micros <= 999999.
Proof.
intros h m s micros; unfold valid_time.
repeat rewrite andb_true_iff.
repeat rewrite z_le_bool_true_iff.
reflexivity.
Qed.

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

Definition time_in_range_bool (time : Z) : bool :=
  (0 <=? time) && (time <=? micros_per_day).

Lemma time_in_range_bool_true_iff :
  forall time,
    time_in_range_bool time = true <-> 0 <= time <= micros_per_day.
Proof.
intro time; unfold time_in_range_bool.
rewrite andb_true_iff, Z.leb_le, Z.leb_le; reflexivity.
Qed.

Definition timestamp_from_ymdhms y m d h minute s micros :=
  if andb (valid_ymd y m d) (valid_time h minute s micros)
  then timestamp_checked
         (days_from_civil y m d * micros_per_day
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

Definition timestamp_add_microseconds_checked timestamp micros :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_microseconds timestamp micros).

Definition timestamp_add_seconds_checked timestamp seconds :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_seconds timestamp seconds).

Definition timestamp_add_minutes_checked timestamp minutes :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_minutes timestamp minutes).

Definition timestamp_add_hours_checked timestamp hours :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_hours timestamp hours).

Definition timestamp_add_days_checked timestamp days :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_days timestamp days).

Definition timestamp_add_months_checked timestamp months :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_months timestamp months).

Definition timestamp_add_years_checked timestamp years :=
  if timestamp_is_infinity_bool timestamp
  then Some timestamp
  else timestamp_checked (timestamp_add_years timestamp years).

Definition cast_date_to_timestamp_checked date :=
  if date_is_neg_infinity_bool date then Some postgres_timestamp_neg_infinity
  else if date_is_pos_infinity_bool date then Some postgres_timestamp_pos_infinity
  else timestamp_checked (cast_date_to_timestamp date).

Definition cast_timestamp_to_date_checked timestamp :=
  if timestamp_is_neg_infinity_bool timestamp then Some postgres_date_neg_infinity
  else if timestamp_is_pos_infinity_bool timestamp then Some postgres_date_pos_infinity
  else date_checked (cast_timestamp_to_date timestamp).

(** PostgreSQL 17 cross-type DATE/TIMESTAMP comparison is deliberately not a
    checked DATE-to-TIMESTAMP cast.  [date_cmp_timestamp_internal] asks the
    conversion for an overflow direction and orders an overflowing finite
    date just inside the corresponding timestamp infinity.  Thus a positive
    overflow is greater than every finite timestamp but less than +infinity;
    symmetrically, a negative overflow is less than every finite timestamp
    but greater than -infinity.  PostgreSQL's currently valid DATE range can
    only reach the positive case, because DATE and TIMESTAMP share their
    finite lower boundary, but keeping both directions makes the ordering
    total and states the internal contract exactly.

    This definition uses the translated Unix-epoch carriers above.  Finite
    in-range dates compare at midnight.  The explicit special-value branches
    preserve DATE/TIMESTAMP +/-infinity equality without treating an
    overflowing finite date as infinity. *)
Definition date_cmp_timestamp_internal
    (date timestamp : Z) : comparison :=
  if date_is_neg_infinity_bool date then
    if timestamp_is_neg_infinity_bool timestamp then Eq else Lt
  else if date_is_pos_infinity_bool date then
    if timestamp_is_pos_infinity_bool timestamp then Eq else Gt
  else
    let midnight := cast_date_to_timestamp date in
    if midnight <? postgres_timestamp_min then
      if timestamp_is_neg_infinity_bool timestamp then Gt else Lt
    else if midnight <? postgres_timestamp_end then
      Z.compare midnight timestamp
    else
      if timestamp_is_pos_infinity_bool timestamp then Lt else Gt.

Definition date_lte_timestamp_bool (date timestamp : Z) : bool :=
  match date_cmp_timestamp_internal date timestamp with
  | Gt => false
  | Eq | Lt => true
  end.

Definition date_lt_timestamp_bool (date timestamp : Z) : bool :=
  match date_cmp_timestamp_internal date timestamp with
  | Lt => true
  | Eq | Gt => false
  end.

Definition date_gt_timestamp_bool (date timestamp : Z) : bool :=
  match date_cmp_timestamp_internal date timestamp with
  | Gt => true
  | Eq | Lt => false
  end.

Definition date_gte_timestamp_bool (date timestamp : Z) : bool :=
  match date_cmp_timestamp_internal date timestamp with
  | Lt => false
  | Eq | Gt => true
  end.

Lemma date_lt_timestamp_bool_spec :
  forall date timestamp,
    date_lt_timestamp_bool date timestamp = true <->
    date_cmp_timestamp_internal date timestamp = Lt.
Proof.
intros date timestamp; unfold date_lt_timestamp_bool.
destruct (date_cmp_timestamp_internal date timestamp);
  split; intro H; try reflexivity; discriminate.
Qed.

Lemma date_lte_timestamp_bool_spec :
  forall date timestamp,
    date_lte_timestamp_bool date timestamp = true <->
    date_cmp_timestamp_internal date timestamp <> Gt.
Proof.
intros date timestamp; unfold date_lte_timestamp_bool.
destruct (date_cmp_timestamp_internal date timestamp);
  split; intro H; try reflexivity; try discriminate; congruence.
Qed.

Lemma date_gt_timestamp_bool_spec :
  forall date timestamp,
    date_gt_timestamp_bool date timestamp = true <->
    date_cmp_timestamp_internal date timestamp = Gt.
Proof.
intros date timestamp; unfold date_gt_timestamp_bool.
destruct (date_cmp_timestamp_internal date timestamp);
  split; intro H; try reflexivity; discriminate.
Qed.

Lemma date_gte_timestamp_bool_spec :
  forall date timestamp,
    date_gte_timestamp_bool date timestamp = true <->
    date_cmp_timestamp_internal date timestamp <> Lt.
Proof.
intros date timestamp; unfold date_gte_timestamp_bool.
destruct (date_cmp_timestamp_internal date timestamp);
  split; intro H; try reflexivity; try discriminate; congruence.
Qed.
