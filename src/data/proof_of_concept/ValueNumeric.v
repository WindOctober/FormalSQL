(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(************************************************************************************)

From Stdlib Require Import ZArith List QArith Qcanon.
Require Import OrderedSet.

Open Scope Z_scope.

(**
  Finite PostgreSQL NUMERIC values.

  [Qc] gives a canonical representation of an arbitrary-precision rational. Logos
  only constructs finite decimal rationals through [numeric_of_scaled], but using
  the canonical carrier is important: SQL numeric equality identifies 1, 1.0 and
  1.00, and the ordered carrier used by bags must make the same identification.

  PostgreSQL additionally tracks a display scale (dscale) which is not part of
  numeric equality but affects scale-sensitive operations such as division.  It
  therefore cannot be stored in this ordered carrier without breaking SQL
  DISTINCT/GROUP BY semantics.  Scale-sensitive operations below receive dscale
  explicitly; a frontend must reject them when it cannot determine that metadata.

  PostgreSQL's special NUMERIC values NaN and +/-Infinity are deliberately absent
  from this datatype. Frontends must reject them before lowering.
*)
Definition numeric : Set := Qc.

Definition numeric_compare : numeric -> numeric -> comparison := Qccompare.

Definition Onumeric : Oset.Rcd numeric.
Proof.
split with numeric_compare.
- intros n1 n2; unfold numeric_compare.
  case_eq (Qccompare n1 n2); intro Hcompare.
  + now apply (proj2 (Qceq_alt n1 n2)).
  + intro Heq; subst n2.
    assert (Qccompare n1 n1 = Eq) as Hrefl.
    { apply (proj1 (Qceq_alt n1 n1)); reflexivity. }
    rewrite Hcompare in Hrefl; discriminate.
  + intro Heq; subst n2.
    assert (Qccompare n1 n1 = Eq) as Hrefl.
    { apply (proj1 (Qceq_alt n1 n1)); reflexivity. }
    rewrite Hcompare in Hrefl; discriminate.
- intros n1 n2 n3 H12 H23.
  apply (proj1 (Qclt_alt n1 n3)).
  eapply Qclt_trans.
  + now apply (proj2 (Qclt_alt n1 n2)).
  + now apply (proj2 (Qclt_alt n2 n3)).
- intros n1 n2; unfold numeric_compare, Qccompare.
  rewrite <- Qcompare_antisym.
  destruct (Qcompare n1 n2); reflexivity.
Defined.

Definition numeric_eqb (n1 n2 : numeric) : bool :=
  match numeric_compare n1 n2 with
  | Eq => true
  | Lt | Gt => false
  end.

Definition numeric_zero : numeric := Q2Qc 0.
Definition numeric_of_Z (z : Z) : numeric := Q2Qc (inject_Z z).

Definition numeric_of_scaled (coeff scale : Z) : numeric :=
  if 0 <=? scale
  then Qcdiv (numeric_of_Z coeff) (numeric_of_Z (Z.pow 10 scale))
  else Qcmult (numeric_of_Z coeff) (numeric_of_Z (Z.pow 10 (- scale))).

Definition numeric_add (n1 n2 : numeric) : numeric := Qcplus n1 n2.
Definition numeric_sub (n1 n2 : numeric) : numeric := Qcminus n1 n2.
Definition numeric_mul (n1 n2 : numeric) : numeric := Qcmult n1 n2.
Definition numeric_opp (n : numeric) : numeric := Qcopp n.

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

Definition numeric_scale_factor (scale : Z) : numeric :=
  if 0 <=? scale
  then numeric_of_Z (Z.pow 10 scale)
  else Qcdiv (numeric_of_Z 1) (numeric_of_Z (Z.pow 10 (- scale))).

Definition numeric_rounded_coeff (n : numeric) (scale : Z) : Z :=
  let scaled := this (Qcmult n (numeric_scale_factor scale)) in
  numeric_round_quot (Qnum scaled) (Zpos (Qden scaled)).

Definition numeric_round_to_scale (n : numeric) (scale : Z) : numeric :=
  numeric_of_scaled (numeric_rounded_coeff n scale) scale.

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
  let q := this n in
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
  else None.

Fixpoint numeric_digit_count_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 1
  | S fuel' => if z <? 10 then 1 else 1 + numeric_digit_count_fuel fuel' (z / 10)
  end.

Definition numeric_digit_count (z : Z) : Z :=
  numeric_digit_count_fuel (S (Z.to_nat (Z.log2 (Z.abs z + 1)))) (Z.abs z).

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
  if numeric_eqb n2 numeric_zero
  then None
  else
    match numeric_pg_div_scale n1 dscale1 n2 dscale2 with
    | Some scale => Some (numeric_round_to_scale (Qcdiv n1 n2) scale)
    | None => None
    end.

Definition numeric_div_by_Z (n : numeric) (z : Z) : option numeric :=
  numeric_div_at_scales n 0 (numeric_of_Z z) 0.

Fixpoint numeric_sum (values : list numeric) : numeric :=
  match values with
  | nil => numeric_zero
  | value :: rest => numeric_add value (numeric_sum rest)
  end.
