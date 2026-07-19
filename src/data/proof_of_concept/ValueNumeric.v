(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(************************************************************************************)

From Stdlib Require Import ZArith List QArith Qcanon Lia.
Require Import OrderedSet.

Open Scope Z_scope.

(**
  PostgreSQL NUMERIC values needed by constrained NUMERIC/DECIMAL columns.

  [Qc] gives a canonical representation of an arbitrary-precision finite
  rational. Logos only constructs finite decimal rationals through
  [numeric_of_scaled], but using the canonical carrier is important: SQL
  numeric equality identifies 1, 1.0 and 1.00, and the ordered carrier used by
  bags must make the same identification.  PostgreSQL also permits [NaN] in a
  NUMERIC column even when it has a finite precision/scale typmod, so NaN is a
  first-class constructor rather than an out-of-band rational sentinel.

  PostgreSQL additionally tracks a display scale (dscale) which is not part of
  numeric equality but affects scale-sensitive operations such as division.  It
  therefore cannot be stored in this ordered carrier without breaking SQL
  DISTINCT/GROUP BY semantics.  Scale-sensitive operations below receive dscale
  explicitly; a frontend must reject them when it cannot determine that metadata.

  PostgreSQL numeric infinities are also first-class values.  They cannot be
  stored in a constrained NUMERIC/DECIMAL column, but they can be produced by
  operations such as EXTRACT(YEAR FROM DATE 'infinity').  PostgreSQL orders the
  four classes as -Infinity, finite values, Infinity, NaN.
*)
Inductive numeric : Set :=
  | NumericNegInfinity : numeric
  | NumericFinite : Qc -> numeric
  | NumericPosInfinity : numeric
  | NumericNaN : numeric.

Definition numeric_compare (n1 n2 : numeric) : comparison :=
  match n1, n2 with
  | NumericNegInfinity, NumericNegInfinity => Eq
  | NumericNegInfinity, _ => Lt
  | _, NumericNegInfinity => Gt
  | NumericFinite q1, NumericFinite q2 => Qccompare q1 q2
  | NumericFinite _, _ => Lt
  | _, NumericFinite _ => Gt
  | NumericPosInfinity, NumericPosInfinity => Eq
  | NumericPosInfinity, NumericNaN => Lt
  | NumericNaN, NumericPosInfinity => Gt
  | NumericNaN, NumericNaN => Eq
  end.

Definition Onumeric : Oset.Rcd numeric.
Proof.
split with numeric_compare.
- intros n1 n2; destruct n1 as [|q1| |]; destruct n2 as [|q2| |];
    simpl; try reflexivity; try discriminate.
  case_eq (Qccompare q1 q2); intro Hcompare.
  + apply f_equal. now apply (proj2 (Qceq_alt q1 q2)).
  + intro Heq; inversion Heq; subst q2.
    assert (Qccompare q1 q1 = Eq) as Hrefl.
    { apply (proj1 (Qceq_alt q1 q1)); reflexivity. }
    rewrite Hcompare in Hrefl; discriminate.
  + intro Heq; inversion Heq; subst q2.
    assert (Qccompare q1 q1 = Eq) as Hrefl.
    { apply (proj1 (Qceq_alt q1 q1)); reflexivity. }
    rewrite Hcompare in Hrefl; discriminate.
- intros n1 n2 n3 H12 H23.
  destruct n1 as [|q1| |]; destruct n2 as [|q2| |];
    destruct n3 as [|q3| |]; simpl in *; try discriminate; try reflexivity.
  apply (proj1 (Qclt_alt q1 q3)).
  eapply Qclt_trans.
  + now apply (proj2 (Qclt_alt q1 q2)).
  + now apply (proj2 (Qclt_alt q2 q3)).
- intros n1 n2; destruct n1 as [|q1| |]; destruct n2 as [|q2| |];
    simpl; try reflexivity.
  unfold Qccompare.
  rewrite <- Qcompare_antisym.
  destruct (Qcompare q1 q2); reflexivity.
Defined.

Definition numeric_eqb (n1 n2 : numeric) : bool :=
  match numeric_compare n1 n2 with
  | Eq => true
  | Lt | Gt => false
  end.

Definition numeric_is_nan (n : numeric) : bool :=
  match n with NumericNaN => true | _ => false end.

Definition numeric_zero : numeric := NumericFinite (Q2Qc 0).
Definition numeric_of_Z (z : Z) : numeric := NumericFinite (Q2Qc (inject_Z z)).

Definition numeric_of_scaled (coeff scale : Z) : numeric :=
  NumericFinite
    (if 0 <=? scale
     then Qcdiv (Q2Qc (inject_Z coeff))
            (Q2Qc (inject_Z (Z.pow 10 scale)))
     else Qcmult (Q2Qc (inject_Z coeff))
            (Q2Qc (inject_Z (Z.pow 10 (- scale))))).

Definition numeric_add (n1 n2 : numeric) : numeric :=
  match n1, n2 with
  | NumericFinite q1, NumericFinite q2 => NumericFinite (Qcplus q1 q2)
  | NumericNaN, _ | _, NumericNaN => NumericNaN
  | NumericNegInfinity, NumericPosInfinity
  | NumericPosInfinity, NumericNegInfinity => NumericNaN
  | NumericNegInfinity, _ | _, NumericNegInfinity => NumericNegInfinity
  | NumericPosInfinity, _ | _, NumericPosInfinity => NumericPosInfinity
  end.

Definition numeric_opp (n : numeric) : numeric :=
  match n with
  | NumericNegInfinity => NumericPosInfinity
  | NumericFinite q => NumericFinite (Qcopp q)
  | NumericPosInfinity => NumericNegInfinity
  | NumericNaN => NumericNaN
  end.

Definition numeric_sub (n1 n2 : numeric) : numeric :=
  numeric_add n1 (numeric_opp n2).

Definition numeric_sign (n : numeric) : comparison :=
  match n with
  | NumericNegInfinity => Lt
  | NumericFinite q => Qccompare q (Q2Qc 0)
  | NumericPosInfinity => Gt
  | NumericNaN => Eq
  end.

Definition numeric_mul_infinity (negative : bool) (other : numeric) : numeric :=
  match numeric_sign other with
  | Eq => NumericNaN
  | Lt => if negative then NumericPosInfinity else NumericNegInfinity
  | Gt => if negative then NumericNegInfinity else NumericPosInfinity
  end.

Definition numeric_mul (n1 n2 : numeric) : numeric :=
  match n1, n2 with
  | NumericFinite q1, NumericFinite q2 => NumericFinite (Qcmult q1 q2)
  | NumericNaN, _ | _, NumericNaN => NumericNaN
  | NumericNegInfinity, other => numeric_mul_infinity true other
  | NumericPosInfinity, other => numeric_mul_infinity false other
  | other, NumericNegInfinity => numeric_mul_infinity true other
  | other, NumericPosInfinity => numeric_mul_infinity false other
  end.

Definition numeric_max (n1 n2 : numeric) : numeric :=
  match numeric_compare n1 n2 with Lt => n2 | Eq | Gt => n1 end.

Definition numeric_min (n1 n2 : numeric) : numeric :=
  match numeric_compare n1 n2 with Gt => n2 | Eq | Lt => n1 end.

(** PostgreSQL NUMERIC rounds ties away from zero. *)
Definition numeric_round_quot (numerator denominator : Z) : Z :=
  let quotient := Z.quot numerator denominator in
  let remainder := Z.rem numerator denominator in
  if Z.geb (2 * Z.abs remainder) (Z.abs denominator)
  then quotient + if Z.ltb (numerator * denominator) 0 then -1 else 1
  else quotient.

Definition numeric_scale_factor (scale : Z) : Qc :=
  if 0 <=? scale
  then Q2Qc (inject_Z (Z.pow 10 scale))
  else Qcdiv (Q2Qc 1) (Q2Qc (inject_Z (Z.pow 10 (- scale)))).

Definition numeric_finite_rounded_coeff (q : Qc) (scale : Z) : Z :=
  let scaled := this (Qcmult q (numeric_scale_factor scale)) in
  numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)).

Definition numeric_rounded_coeff (n : numeric) (scale : Z) : option Z :=
  match n with
  | NumericFinite q => Some (numeric_finite_rounded_coeff q scale)
  | _ => None
  end.

Lemma numeric_rounded_coeff_finite_some q scale :
  numeric_rounded_coeff (NumericFinite q) scale =
  Some (numeric_finite_rounded_coeff q scale).
Proof. reflexivity. Qed.

Definition numeric_round_to_scale (n : numeric) (scale : Z) : numeric :=
  match n with
  | NumericFinite _ =>
      match numeric_rounded_coeff n scale with
      | Some coeff => numeric_of_scaled coeff scale
      | None => NumericNaN
      end
  | _ => n
  end.

(** Recover the minimal finite-decimal coefficient and scale. *)
Fixpoint numeric_remove_factor
    (fuel : nat) (factor value : Z) : nat * Z :=
  match fuel with
  | O => (O, value)
  | S fuel' =>
      if (value mod factor =? 0)%Z
      then
        let '(count, rest) := numeric_remove_factor fuel' factor (value / factor) in
        (S count, rest)
      else (O, value)
  end.

Definition numeric_decimal_parts (n : numeric) : option (Z * Z) :=
  match n with
  | NumericFinite q =>
      let q := this q in
      let denominator := Zpos (Qden q) in
      let fuel := S (Pos.size_nat (Qden q)) in
      let '(twos, after_twos) := numeric_remove_factor fuel 2 denominator in
      let '(fives, rest) := numeric_remove_factor fuel 5 after_twos in
      if rest =? 1 then
        let twos_z := Z.of_nat twos in
        let fives_z := Z.of_nat fives in
        let scale := Z.max twos_z fives_z in
        let coeff :=
          Qnum q * Z.pow 2 (scale - twos_z) * Z.pow 5 (scale - fives_z) in
        Some (coeff, scale)
      else None
  | _ => None
  end.

Fixpoint numeric_digit_count_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 1
  | S fuel' => if z <? 10 then 1 else 1 + numeric_digit_count_fuel fuel' (z / 10)
  end.

Definition numeric_digit_count (z : Z) : Z :=
  numeric_digit_count_fuel (S (Z.to_nat (Z.log2 (Z.abs z + 1)))) (Z.abs z).

(**
  PostgreSQL's unconstrained [NUMERIC] carrier is arbitrary precision only up
  to the implementation limits of 131072 digits before the decimal point and
  16383 digits after it.  The canonical [Qc] carrier intentionally forgets
  display-only trailing zeroes, so this predicate checks the significant
  finite-decimal value.  Operations whose input display scale matters pass
  that metadata separately.
*)
Definition postgres_numeric_max_integer_digits : Z := 131072.
Definition postgres_numeric_max_fractional_digits : Z := 16383.

Definition numeric_integer_digit_count (coeff scale : Z) : Z :=
  if coeff =? 0 then 0 else Z.max 0 (numeric_digit_count coeff - scale).

Definition numeric_display_scale_valid_bool (scale : Z) : bool :=
  (0 <=? scale) && (scale <=? postgres_numeric_max_fractional_digits).

Definition numeric_runtime_fits_bool (n : numeric) : bool :=
  match n with
  | NumericNegInfinity | NumericPosInfinity | NumericNaN => true
  | NumericFinite _ =>
      match numeric_decimal_parts n with
      | Some (coeff, scale) =>
          numeric_display_scale_valid_bool scale
          && (numeric_integer_digit_count coeff scale
              <=? postgres_numeric_max_integer_digits)
      | None => false
      end
  end.

(*
   PostgreSQL NUMERIC/DECIMAL division has no SQL-standard fixed result scale.
   PostgreSQL chooses a display scale in
   src/backend/utils/adt/numeric.c:select_div_scale using its base-10000
   NumericVar representation:

     rscale = NUMERIC_MIN_SIG_DIGITS - qweight * DEC_DIGITS
     rscale = max(rscale, left.dscale, right.dscale,
                  NUMERIC_MIN_DISPLAY_SCALE)
     rscale = min(rscale, NUMERIC_MAX_DISPLAY_SCALE)

   The constants below mirror PostgreSQL's default
   src/include/utils/numeric.h configuration: DEC_DIGITS = 4,
   NUMERIC_MIN_SIG_DIGITS = 16, NUMERIC_MIN_DISPLAY_SCALE = 0, and
   NUMERIC_MAX_DISPLAY_SCALE = NUMERIC_MAX_PRECISION = 1000.
*)
Definition postgres_numeric_dec_digits : Z := 4.
Definition postgres_numeric_min_sig_digits : Z := 16.
Definition postgres_numeric_min_display_scale : Z := 0.
Definition postgres_numeric_max_display_scale : Z := 1000.

Definition numeric_pg_weight (coeff scale : Z) : Z :=
  if coeff =? 0 then 0
  else (numeric_digit_count coeff - 1 - scale) / postgres_numeric_dec_digits.

Definition numeric_shift_by_pow10 (z exponent : Z) : Z :=
  if 0 <=? exponent then z / Z.pow 10 exponent else z * Z.pow 10 (- exponent).

Definition numeric_pg_first_digit (coeff scale : Z) : Z :=
  if coeff =? 0 then 0
  else
    numeric_shift_by_pow10
      (Z.abs coeff)
      (scale + numeric_pg_weight coeff scale * postgres_numeric_dec_digits).

Definition numeric_pg_div_scale
    (n1 : numeric) (dscale1 : Z) (n2 : numeric) (dscale2 : Z) : option Z :=
  match numeric_decimal_parts n1, numeric_decimal_parts n2 with
  | Some (coeff1, scale1), Some (coeff2, scale2) =>
      let weight1 := numeric_pg_weight coeff1 scale1 in
      let weight2 := numeric_pg_weight coeff2 scale2 in
      let firstdigit1 := numeric_pg_first_digit coeff1 scale1 in
      let firstdigit2 := numeric_pg_first_digit coeff2 scale2 in
      let qweight :=
        if firstdigit1 <=? firstdigit2 then weight1 - weight2 - 1 else weight1 - weight2 in
      let rscale := postgres_numeric_min_sig_digits - qweight * postgres_numeric_dec_digits in
      let rscale := Z.max rscale dscale1 in
      let rscale := Z.max rscale dscale2 in
      let rscale := Z.max rscale postgres_numeric_min_display_scale in
      Some (Z.min rscale postgres_numeric_max_display_scale)
  | _, _ => None
  end.

Definition numeric_div_at_scales
    (n1 : numeric) (dscale1 : Z) (n2 : numeric) (dscale2 : Z) : option numeric :=
  match n1, n2 with
  | NumericNaN, _ | _, NumericNaN => Some NumericNaN
  | NumericNegInfinity, NumericNegInfinity
  | NumericNegInfinity, NumericPosInfinity
  | NumericPosInfinity, NumericNegInfinity
  | NumericPosInfinity, NumericPosInfinity => Some NumericNaN
  | NumericNegInfinity, NumericFinite q2 =>
      match Qccompare q2 (Q2Qc 0) with
      | Eq => None
      | Lt => Some NumericPosInfinity
      | Gt => Some NumericNegInfinity
      end
  | NumericPosInfinity, NumericFinite q2 =>
      match Qccompare q2 (Q2Qc 0) with
      | Eq => None
      | Lt => Some NumericNegInfinity
      | Gt => Some NumericPosInfinity
      end
  | NumericFinite _, NumericNegInfinity
  | NumericFinite _, NumericPosInfinity => Some numeric_zero
  | NumericFinite q1, NumericFinite q2 =>
      if numeric_eqb n2 numeric_zero
      then None
      else
        match numeric_pg_div_scale n1 dscale1 n2 dscale2 with
        | Some scale =>
            Some (numeric_round_to_scale (NumericFinite (Qcdiv q1 q2)) scale)
        | None => None
        end
  end.

(** PostgreSQL retains the scale selected for a successful NUMERIC division
    as the result's display scale.  The value carrier above intentionally
    stores only the mathematical numeric value, so a surrounding division
    must reconstruct this metadata from the same operands.  Special results
    use PostgreSQL's scale-independent constants (their dscale is ignored),
    while a finite quotient uses exactly [numeric_pg_div_scale]. *)
Definition numeric_div_result_dscale
    (n1 : numeric) (dscale1 : Z) (n2 : numeric) (dscale2 : Z) : option Z :=
  match numeric_div_at_scales n1 dscale1 n2 dscale2 with
  | None => None
  | Some _ =>
      match n1, n2 with
      | NumericFinite _, NumericFinite _ =>
          numeric_pg_div_scale n1 dscale1 n2 dscale2
      | _, _ => Some 0
      end
  end.

Definition numeric_div_by_Z (n : numeric) (z : Z) : option numeric :=
  numeric_div_at_scales n 0 (numeric_of_Z z) 0.

(** Round the nonnegative square root of a finite PostgreSQL numeric to an
    explicit decimal display scale.  [sqrt_var] computes one guard digit and
    rounds half away from zero; since square roots here are nonnegative, the
    integer comparison against [(floor + 1/2)^2] is the same rule without an
    irrational carrier. *)
Definition numeric_sqrt_at_scale
    (n : numeric) (scale : Z) : option numeric :=
  match n with
  | NumericNegInfinity => None
  | NumericPosInfinity => Some NumericPosInfinity
  | NumericNaN => Some NumericNaN
  | NumericFinite q =>
      if (scale <? 0)%Z then None else
      let q := this q in
      if (Qnum q <? 0)%Z then None else
      let factor := Z.pow 10 scale in
      let scaled_numerator := Qnum q * factor * factor in
      let denominator := Zpos (Qden q) in
      let lower := Z.sqrt (Z.div scaled_numerator denominator) in
      let midpoint_twice := 2 * lower + 1 in
      let rounded :=
        if denominator * midpoint_twice * midpoint_twice
             <=? 4 * scaled_numerator
        then lower + 1
        else lower in
      Some (numeric_of_scaled rounded scale)
  end.

(** PostgreSQL's [power(int8, 0.5::numeric)] resolves to the
    [power(numeric, numeric)] overload.  For a nonnegative signed BIGINT the
    result has decimal weight [floor ((digits(base) - 1) / 2)].  [power_var]
    consequently selects [16 - weight] fractional digits (the exponent's
    display scale is only one and never dominates in the BIGINT range).

    Keeping this finite result scale is observable: for example, a square root
    just below an integer-plus-one-half can round to exactly one-half at the
    POWER result scale, after which an explicit NUMERIC-to-INTEGER cast rounds
    upward. *)
Definition numeric_power_half_int64_scale (base : Z) : Z :=
  Z.min postgres_numeric_max_display_scale
    (Z.max
      (postgres_numeric_min_sig_digits -
       (numeric_digit_count base - 1) / 2)
      1).

Definition numeric_power_half_int64 (base : Z) : option numeric :=
  if base <? 0 then None
  else numeric_sqrt_at_scale
         (numeric_of_Z base) (numeric_power_half_int64_scale base).

Lemma numeric_power_half_int64_scale_nonnegative base :
  0 <= numeric_power_half_int64_scale base.
Proof.
  unfold numeric_power_half_int64_scale,
    postgres_numeric_max_display_scale.
  pose proof (Z.le_max_r
    (postgres_numeric_min_sig_digits -
     (numeric_digit_count base - 1) / 2) 1).
  lia.
Qed.

(** Finalization shared by integral variance and standard-deviation
    aggregates.  The transition fields are exact mathematical count, sum,
    and sum of squares.  Final numeric arithmetic computes
    [N * sumX2 - sumX^2], divided by [N^2] for population or [N * (N-1)] for
    sample statistics, with PostgreSQL's division scale.  A nonpositive
    numerator is clamped to exact zero. *)
Definition numeric_integer_statistic
    (count sum sum_squares : Z) (variance sample : bool) : option numeric :=
  if count =? 0 then None
  else if sample && (count <=? 1) then None
  else
    let numerator := count * sum_squares - sum * sum in
    if numerator <=? 0 then Some numeric_zero
    else
      let denominator :=
        if sample then count * (count - 1) else count * count in
      let numerator_numeric := numeric_of_Z numerator in
      let denominator_numeric := numeric_of_Z denominator in
      match numeric_pg_div_scale numerator_numeric 0 denominator_numeric 0,
            numeric_div_at_scales numerator_numeric 0 denominator_numeric 0 with
      | Some scale, Some result =>
          if variance then Some result else numeric_sqrt_at_scale result scale
      | _, _ => None
      end.

(** PostgreSQL's integer STDDEV_SAMP finalizer chooses a NUMERIC display
    scale while dividing the exact variance numerator, then asks sqrt_var to
    return the standard deviation at that same scale.  Ordinary SQL numeric
    equality intentionally discards display scale, but a subsequent NUMERIC
    division needs it. Retain the locally chosen scale so compositional scalar
    lowering can consume the ordinary STDDEV_SAMP result exactly. *)
Definition numeric_integer_stddev_samp_with_scale
    (count sum sum_squares : Z) : option (numeric * Z) :=
  if count =? 0 then None
  else if count <=? 1 then None
  else
    let numerator := count * sum_squares - sum * sum in
    if numerator <=? 0 then Some (numeric_zero, 0)
    else
      let denominator := count * (count - 1) in
      let numerator_numeric := numeric_of_Z numerator in
      let denominator_numeric := numeric_of_Z denominator in
      match numeric_pg_div_scale numerator_numeric 0 denominator_numeric 0,
            numeric_div_at_scales numerator_numeric 0 denominator_numeric 0 with
      | Some scale, Some variance =>
          match numeric_sqrt_at_scale variance scale with
          | Some stddev => Some (stddev, scale)
          | None => None
          end
      | _, _ => None
      end.

(** Exact transition state for PostgreSQL's general NUMERIC statistical
    aggregates when every finite input has one known display scale.  The two
    sums are stored as integer coefficients: [sum_coeff / 10^input_scale] is
    [sumX], and [sum_square_coeff / 10^(2*input_scale)] is [sumX2].  This is
    the same exact arithmetic performed by [NumericSumAccum], without making
    display scale part of SQL numeric equality.

    PostgreSQL counts NaN and infinities separately from finite values.  A
    constrained NUMERIC/DECIMAL column can contain NaN but rejects either
    infinity; keeping one explicit special count here nevertheless makes the
    finalizer faithful for every special value and lets the constrained-value
    checker reject the unreachable infinity cases independently. *)
Definition numeric_scale_stats_state : Type :=
  (Z * (Z * (Z * Z)))%type.

Definition numeric_scale_stats_initial : numeric_scale_stats_state :=
  (0, (0, (0, 0))).

Definition numeric_scale_stats_total_count
    (state : numeric_scale_stats_state) : Z :=
  let '(finite_count, (special_count, _)) := state in
  finite_count + special_count.

Definition numeric_scale_stats_transition
    (input_scale : Z)
    (state : numeric_scale_stats_state)
    (next : numeric) : numeric_scale_stats_state :=
  let '(finite_count, (special_count, (sum_coeff, sum_square_coeff))) := state in
  match next with
  | NumericFinite q =>
      let coeff := numeric_finite_rounded_coeff q input_scale in
      (finite_count + 1,
       (special_count,
        (sum_coeff + coeff, sum_square_coeff + coeff * coeff)))
  | NumericNegInfinity | NumericPosInfinity | NumericNaN =>
      (finite_count, (special_count + 1, (sum_coeff, sum_square_coeff)))
  end.

(** PostgreSQL [numeric_stddev_internal] first squares [sumX] and multiplies
    [sumX2] by N at [2 * input_scale].  Exact fixed-scale coefficients make
    both products exact at that rscale.  It then computes

      (N * sumX2 - sumX^2) / (N * (N - 1)),

    clamps a nonpositive numerator to exact zero, chooses the division scale
    with [select_div_scale], and rounds [sqrt_var] at that same scale. *)
Definition numeric_stddev_samp_finite_at_scale
    (input_scale finite_count sum_coeff sum_square_coeff : Z)
    : option numeric :=
  if negb (numeric_display_scale_valid_bool input_scale) then None
  else
    let product_scale := 2 * input_scale in
    if negb (numeric_display_scale_valid_bool product_scale) then None
    else
      let numerator_coeff :=
        finite_count * sum_square_coeff - sum_coeff * sum_coeff in
      if numerator_coeff <=? 0 then Some numeric_zero
      else
        let numerator := numeric_of_scaled numerator_coeff product_scale in
        let denominator :=
          numeric_of_Z (finite_count * (finite_count - 1)) in
        match numeric_pg_div_scale numerator product_scale denominator 0,
              numeric_div_at_scales numerator product_scale denominator 0 with
        | Some result_scale, Some variance =>
            numeric_sqrt_at_scale variance result_scale
        | _, _ => None
        end.

Definition numeric_stddev_samp_from_scale_state
    (input_scale : Z) (state : numeric_scale_stats_state) : option numeric :=
  let '(finite_count,
        (special_count, (sum_coeff, sum_square_coeff))) := state in
  let total_count := numeric_scale_stats_total_count state in
  if total_count <=? 1 then None
  else if 0 <? special_count then Some NumericNaN
  else numeric_stddev_samp_finite_at_scale
         input_scale finite_count sum_coeff sum_square_coeff.

Fixpoint numeric_sum (values : list numeric) : numeric :=
  match values with
  | nil => numeric_zero
  | value :: rest => numeric_add value (numeric_sum rest)
  end.
