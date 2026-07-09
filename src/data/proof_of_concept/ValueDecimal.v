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

Require Import ZArith List.
Require Import OrderedSet.

Open Scope Z_scope.

(**
   Exact fixed-scale decimal payloads.

   [Decimal precision scale coeff] denotes [coeff / 10^scale] stored under
   SQL typmod DECIMAL(precision, scale).  [decimal_checked] is the refinement
   constructor: it produces a value only when scale and coefficient fit the
   declared typmod.  SQL comparison predicates below use numeric comparison
   after rescaling.  The ordered-set instance [Odecimal] remains structural
   over [(precision, scale, coeff)] because FormalSQL finite bags require an
   order whose [Eq] branch implies Coq equality.
*)
Definition decimal_pow10 (scale : Z) : Z :=
  Z.pow 10 scale.

Definition decimal_max_precision : Z := 1000.
Definition decimal_min_scale : Z := 0.
Definition decimal_max_scale : Z := 1000.

Definition decimal_fits_typmod_bool (precision scale coeff : Z) : bool :=
  (1 <=? precision)
  && (precision <=? decimal_max_precision)
  && (0 <=? scale)
  && (scale <=? decimal_max_scale)
  && (Z.abs coeff <? decimal_pow10 precision).

Record decimal : Set := Decimal {
  decimal_precision : Z;
  decimal_scale : Z;
  decimal_coeff : Z
}.

(*
   TODO(Logos): upgrade this to a proof-carrying refinement record once the
   surrounding ordered-set and bag instances can absorb the extra proof
   obligations cleanly.  For now, [decimal_checked] is the checked constructor
   used by the lowering pipeline to keep generated Decimal values within the
   modeled DECIMAL(p,s) domain without threading refinement proofs through
   every comparison and aggregation lemma.
*)
Definition decimal_checked (precision scale coeff : Z) : option decimal :=
  if decimal_fits_typmod_bool precision scale coeff
  then Some (Decimal precision scale coeff)
  else None.

Definition decimal_fits_typmod (d : decimal) : Prop :=
  decimal_fits_typmod_bool
    (decimal_precision d) (decimal_scale d) (decimal_coeff d) = true.

Definition decimal_has_scale (d : decimal) (scale : Z) : Prop :=
  decimal_scale d = scale.

Definition decimal_struct_key (d : decimal) :=
  (decimal_precision d, (decimal_scale d, decimal_coeff d)).

Definition decimal_struct_compare d1 d2 :=
  compareAB Z.compare (compareAB Z.compare Z.compare)
    (decimal_struct_key d1) (decimal_struct_key d2).

Definition Odecimal : Oset.Rcd decimal.
Proof.
split with decimal_struct_compare.
- intros [p1 s1 c1] [p2 s2 c2]; unfold decimal_struct_compare, decimal_struct_key; simpl.
  case_eq (Z.compare p1 p2); intro Hp.
  + apply Z.compare_eq in Hp; subst p2.
    case_eq (Z.compare s1 s2); intro Hs.
    * apply Z.compare_eq in Hs; subst s2.
      case_eq (Z.compare c1 c2); intro Hc.
      -- apply Z.compare_eq in Hc; subst c2.
         reflexivity.
      -- intro Heq; inversion Heq; subst.
         rewrite Z.compare_refl in Hc; discriminate.
      -- intro Heq; inversion Heq; subst.
         rewrite Z.compare_refl in Hc; discriminate.
    * intro Heq; inversion Heq; subst.
      rewrite Z.compare_refl in Hs; discriminate.
    * intro Heq; inversion Heq; subst.
      rewrite Z.compare_refl in Hs; discriminate.
  + intro Heq; inversion Heq; subst.
    rewrite Z.compare_refl in Hp; discriminate.
  + intro Heq; inversion Heq; subst.
    rewrite Z.compare_refl in Hp; discriminate.
- intros d1 d2 d3; unfold decimal_struct_compare.
  compareAB_tac.
  + apply (Oset.compare_eq_trans OZ).
  + apply (Oset.compare_eq_lt_trans OZ).
  + apply (Oset.compare_lt_eq_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + destruct b as [s_left c_left].
    destruct b0 as [s_mid c_mid].
    destruct b1 as [s_right c_right].
    apply compareAB_lt_trans.
    * apply (Oset.compare_eq_trans OZ).
    * apply (Oset.compare_eq_lt_trans OZ).
    * apply (Oset.compare_lt_eq_trans OZ).
    * apply (Oset.compare_lt_trans OZ).
    * apply (Oset.compare_lt_trans OZ).
- intros d1 d2; unfold decimal_struct_compare.
  apply compareAB_lt_gt.
  + apply (Oset.compare_lt_gt OZ).
  + apply compareAB_lt_gt; apply (Oset.compare_lt_gt OZ).
Defined.

Definition decimal_compare (d1 d2 : decimal) : comparison :=
  Z.compare
    (decimal_coeff d1 * decimal_pow10 (decimal_scale d2))
    (decimal_coeff d2 * decimal_pow10 (decimal_scale d1)).

Definition decimal_eqb d1 d2 :=
  match decimal_compare d1 d2 with
  | Eq => true
  | _ => false
  end.

Definition decimal_max d1 d2 :=
  match decimal_compare d1 d2 with
  | Lt => d2
  | Eq | Gt => d1
  end.

Definition decimal_min d1 d2 :=
  match decimal_compare d1 d2 with
  | Gt => d2
  | Eq | Lt => d1
  end.

Definition decimal_rescale_coeff (coeff from_scale to_scale : Z) : Z :=
  coeff * decimal_pow10 (to_scale - from_scale).

Definition decimal_common_scale d1 d2 :=
  Z.max (decimal_scale d1) (decimal_scale d2).

Definition decimal_integral_digits d :=
  decimal_precision d - decimal_scale d.

Definition decimal_binary_precision d1 d2 result_scale :=
  Z.max (decimal_integral_digits d1) (decimal_integral_digits d2) + 1 + result_scale.

Fixpoint decimal_digit_count_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 1
  | S fuel' =>
      if z <? 10
      then 1
      else 1 + decimal_digit_count_fuel fuel' (z / 10)
  end.

Definition decimal_digit_count (z : Z) : Z :=
  decimal_digit_count_fuel (Z.to_nat (Z.abs z)) (Z.abs z).

Definition decimal_precision_for_scale (coeff scale : Z) : Z :=
  Z.max 1 (Z.max scale (decimal_digit_count coeff)).

Definition decimal_add d1 d2 :=
  let scale := decimal_common_scale d1 d2 in
  decimal_checked
    (decimal_binary_precision d1 d2 scale)
    scale
    (decimal_rescale_coeff (decimal_coeff d1) (decimal_scale d1) scale
     + decimal_rescale_coeff (decimal_coeff d2) (decimal_scale d2) scale).

Definition decimal_sub d1 d2 :=
  let scale := decimal_common_scale d1 d2 in
  decimal_checked
    (decimal_binary_precision d1 d2 scale)
    scale
    (decimal_rescale_coeff (decimal_coeff d1) (decimal_scale d1) scale
     - decimal_rescale_coeff (decimal_coeff d2) (decimal_scale d2) scale).

Definition decimal_mul d1 d2 :=
  decimal_checked
    (decimal_precision d1 + decimal_precision d2)
    (decimal_scale d1 + decimal_scale d2)
    (decimal_coeff d1 * decimal_coeff d2).

Definition decimal_of_Z z :=
  decimal_checked (Z.max 1 (Z.abs z + 1)) 0 z.

Definition decimal_round_quot (numerator denominator : Z) : Z :=
  let quotient := Z.quot numerator denominator in
  let remainder := Z.rem numerator denominator in
  if Z.geb (2 * Z.abs remainder) (Z.abs denominator)
  then
    quotient
    + if Z.ltb (numerator * denominator) 0 then -1 else 1
  else quotient.

Definition decimal_div_coeff (d1 d2 : decimal) (result_scale : Z) : Z :=
  decimal_round_quot
    (decimal_coeff d1 * decimal_pow10 (decimal_scale d2 + result_scale))
    (decimal_coeff d2 * decimal_pow10 (decimal_scale d1)).

Definition decimal_round_coeff_to_scale (coeff from_scale to_scale : Z) : Z :=
  if from_scale <=? to_scale
  then coeff * decimal_pow10 (to_scale - from_scale)
  else decimal_round_quot coeff (decimal_pow10 (from_scale - to_scale)).

Definition decimal_cast_typmod
    (d : decimal) (result_precision result_scale : Z) : option decimal :=
  decimal_checked
    result_precision
    result_scale
    (decimal_round_coeff_to_scale (decimal_coeff d) (decimal_scale d) result_scale).

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
Definition postgres_numeric_max_display_scale : Z := decimal_max_precision.

Definition decimal_pg_weight (d : decimal) : Z :=
  if Z.eqb (decimal_coeff d) 0 then 0
  else
    (decimal_digit_count (decimal_coeff d) - 1 - decimal_scale d)
    / postgres_numeric_dec_digits.

Definition decimal_shift_by_pow10 (z exponent : Z) : Z :=
  if 0 <=? exponent
  then z / decimal_pow10 exponent
  else z * decimal_pow10 (- exponent).

Definition decimal_pg_first_digit (d : decimal) : Z :=
  if Z.eqb (decimal_coeff d) 0 then 0
  else
    decimal_shift_by_pow10
      (Z.abs (decimal_coeff d))
      (decimal_scale d + decimal_pg_weight d * postgres_numeric_dec_digits).

Definition decimal_pg_div_scale (d1 d2 : decimal) : Z :=
  let weight1 := decimal_pg_weight d1 in
  let weight2 := decimal_pg_weight d2 in
  let firstdigit1 := decimal_pg_first_digit d1 in
  let firstdigit2 := decimal_pg_first_digit d2 in
  let qweight :=
    if firstdigit1 <=? firstdigit2
    then weight1 - weight2 - 1
    else weight1 - weight2 in
  let rscale := postgres_numeric_min_sig_digits - qweight * postgres_numeric_dec_digits in
  let rscale := Z.max rscale (decimal_scale d1) in
  let rscale := Z.max rscale (decimal_scale d2) in
  let rscale := Z.max rscale postgres_numeric_min_display_scale in
  Z.min rscale postgres_numeric_max_display_scale.

Definition decimal_div (d1 d2 : decimal) : option decimal :=
  if Z.eqb (decimal_coeff d2) 0
  then None
  else
    let result_scale := decimal_pg_div_scale d1 d2 in
    let coeff := decimal_div_coeff d1 d2 result_scale in
    (* Bare PostgreSQL numeric division has no DECIMAL(p,s) typmod.  The
       precision stored here is the minimal precision needed to keep the
       FormalSQL decimal payload checked; the PostgreSQL-visible choice is the
       display scale [result_scale]. *)
    decimal_checked
      (decimal_precision_for_scale coeff result_scale)
      result_scale
      coeff.

Definition decimal_div_with_typmod
    (d1 d2 : decimal) (result_precision result_scale : Z) : option decimal :=
  match decimal_div d1 d2 with
  | Some result => decimal_cast_typmod result result_precision result_scale
  | None => None
  end.

Definition decimal_div_by_z (d : decimal) (z result_scale : Z) : option decimal :=
  match decimal_of_Z z with
  | Some dz => decimal_div_with_typmod
      d dz (decimal_integral_digits d + result_scale) result_scale
  | None => None
  end.

Definition decimal_opp d :=
  decimal_checked (decimal_precision d) (decimal_scale d) (Z.opp (decimal_coeff d)).

Definition decimal_zero : decimal :=
  Decimal 1 0 0.

Fixpoint decimal_sum (l : list decimal) : option decimal :=
  match l with
  | nil => Some decimal_zero
  | d :: tl =>
      match decimal_sum tl with
      | Some sum => decimal_add d sum
      | None => None
      end
  end.
