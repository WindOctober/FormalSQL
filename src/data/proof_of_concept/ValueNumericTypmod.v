(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(************************************************************************************)

From Stdlib Require Import ZArith.
Require Export ValueNumeric.

Open Scope Z_scope.

Definition numeric_max_precision : Z := 1000.
Definition numeric_min_scale : Z := -1000.
Definition numeric_max_scale : Z := 1000.

Definition numeric_typmod_valid_bool (precision scale : Z) : bool :=
  (1 <=? precision)
  && (precision <=? numeric_max_precision)
  && (numeric_min_scale <=? scale)
  && (scale <=? numeric_max_scale).

Definition numeric_fits_typmod_bool
    (value : numeric) (precision scale : Z) : bool :=
  numeric_typmod_valid_bool precision scale
  && match value with
     | NumericNaN => true
     | NumericFinite _ =>
         match numeric_rounded_coeff value scale with
         | Some coeff => Z.abs coeff <? Z.pow 10 precision
         | None => false
         end
     | NumericNegInfinity | NumericPosInfinity => false
     end.

Definition numeric_cast_typmod
    (value : numeric) (precision scale : Z) : option numeric :=
  if numeric_fits_typmod_bool value precision scale
  then Some (numeric_round_to_scale value scale)
  else None.

Definition numeric_of_scaled_with_typmod
    (precision scale coeff : Z) : option numeric :=
  numeric_cast_typmod (numeric_of_scaled coeff scale) precision scale.

Definition numeric_div_with_typmod
    (left : numeric) (left_scale : Z)
    (right : numeric) (right_scale : Z)
    (precision scale : Z) : option numeric :=
  match numeric_div_at_scales left left_scale right right_scale with
  | Some result => numeric_cast_typmod result precision scale
  | None => None
  end.
