(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                       LMF, CNRS & Universite Paris-Saclay                       *)
(**                                                                                 *)
(**                        Copyright 2016-2022 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Veronique Benzaken                                             *)
(**                  Evelyne Contejean                                              *)
(**                                                                                 *)
(************************************************************************************)

Require Import ZArith Lia.
Require Import OrderedSet.
From Flocq Require Import IEEE754.Bits IEEE754.BinarySingleNaN.

Open Scope Z_scope.

(**
   SQL REAL/FLOAT and DOUBLE PRECISION are evaluated with Flocq IEEE-754
   binary formats.  SQL-visible values are wrapped in canonical forms rather
   than stored as raw IEEE bit patterns: every NaN is represented by one
   constructor and signed zeros are collapsed to the positive-zero bit pattern.
   This keeps predicate equality, tuple equality, DISTINCT, GROUP BY, and set
   operators on the same PostgreSQL-style equality relation.
*)

Module Type SQL_FLOAT.

Definition raw_float32 := binary32.
Definition raw_float64 := binary64.

Parameter float32 : Set.
Parameter float64 : Set.

Parameter Float32NaN : float32.
Parameter Float64NaN : float64.

Parameter mk_float32 : raw_float32 -> float32.
Parameter mk_float64 : raw_float64 -> float64.
Parameter raw_float32_of : float32 -> raw_float32.
Parameter raw_float64_of : float64 -> raw_float64.

Parameter float32_is_nan : float32 -> bool.
Parameter float64_is_nan : float64 -> bool.
Parameter float32_is_infinite : float32 -> bool.
Parameter float64_is_infinite : float64 -> bool.
Parameter float32_is_zero : float32 -> bool.
Parameter float64_is_zero : float64 -> bool.
Parameter float32_is_nan_true_iff : forall value,
  float32_is_nan value = true <-> value = Float32NaN.
Parameter float64_is_nan_true_iff : forall value,
  float64_is_nan value = true <-> value = Float64NaN.
Parameter float32_is_nan_mk : forall raw,
  float32_is_nan (mk_float32 raw) = Binary.is_nan 24 128 raw.
Parameter float64_is_nan_mk : forall raw,
  float64_is_nan (mk_float64 raw) = Binary.is_nan 53 1024 raw.
Parameter float32_is_infinite_nan :
  float32_is_infinite Float32NaN = false.
Parameter float64_is_infinite_nan :
  float64_is_infinite Float64NaN = false.
Parameter Ofloat32 : Oset.Rcd float32.
Parameter Ofloat64 : Oset.Rcd float64.

Parameter float32_compare : float32 -> float32 -> option comparison.
Parameter float64_compare : float64 -> float64 -> option comparison.
Parameter float32_compare_nan_left : forall value,
  float32_compare Float32NaN value =
    if float32_is_nan value then Some Eq else Some Gt.
Parameter float32_compare_nan_right : forall value,
  float32_compare value Float32NaN =
    if float32_is_nan value then Some Eq else Some Lt.
Parameter float64_compare_nan_left : forall value,
  float64_compare Float64NaN value =
    if float64_is_nan value then Some Eq else Some Gt.
Parameter float64_compare_nan_right : forall value,
  float64_compare value Float64NaN =
    if float64_is_nan value then Some Eq else Some Lt.
Parameter float32_eqb : float32 -> float32 -> bool.
Parameter float64_eqb : float64 -> float64 -> bool.
Parameter float32_ltb : float32 -> float32 -> bool.
Parameter float64_ltb : float64 -> float64 -> bool.
Parameter float32_leb : float32 -> float32 -> bool.
Parameter float64_leb : float64 -> float64 -> bool.

Parameter float32_add : float32 -> float32 -> float32.
Parameter float32_sub : float32 -> float32 -> float32.
Parameter float32_mul : float32 -> float32 -> float32.
Parameter float32_div : float32 -> float32 -> float32.
Parameter float32_opp : float32 -> float32.
Parameter float32_zero : float32.
Parameter float32_of_Z : Z -> float32.
Parameter float32_max : float32 -> float32 -> float32.
Parameter float32_min : float32 -> float32 -> float32.
Parameter float32_add_order_sensitive :
  exists first second third,
    float32_add (float32_add (float32_add float32_zero first) second) third <>
    float32_add (float32_add (float32_add float32_zero first) third) second.
Parameter float64_add : float64 -> float64 -> float64.
Parameter float64_sub : float64 -> float64 -> float64.
Parameter float64_mul : float64 -> float64 -> float64.
Parameter float64_div : float64 -> float64 -> float64.
Parameter float64_opp : float64 -> float64.
Parameter float64_zero : float64.
Parameter float64_of_Z : Z -> float64.
Parameter float32_to_float64 : float32 -> float64.
Parameter float32_to_float64_nan :
  float32_to_float64 Float32NaN = Float64NaN.
Parameter float64_max : float64 -> float64 -> float64.
Parameter float64_min : float64 -> float64 -> float64.
Parameter float32_average_order_sensitive :
  exists first second third,
    float64_div
      (float64_add
        (float64_add
          (float64_add float64_zero (float32_to_float64 first))
          (float32_to_float64 second))
        (float32_to_float64 third))
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)) <>
    float64_div
      (float64_add
        (float64_add
          (float64_add float64_zero (float32_to_float64 first))
          (float32_to_float64 third))
        (float32_to_float64 second))
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)).
Parameter float64_add_order_sensitive :
  exists first second third,
    float64_add (float64_add (float64_add float64_zero first) second) third <>
    float64_add (float64_add (float64_add float64_zero first) third) second.
Parameter float64_average_order_sensitive :
  exists first second third,
    float64_div
      (float64_add (float64_add (float64_add float64_zero first) second) third)
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)) <>
    float64_div
      (float64_add (float64_add (float64_add float64_zero first) third) second)
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)).

End SQL_FLOAT.

Module SqlFloat : SQL_FLOAT.

Definition raw_float32 := binary32.
Definition raw_float64 := binary64.

Inductive float32_impl : Set :=
  | Float32NaN_ : float32_impl
  | Float32Bits_ : Z -> float32_impl.

Inductive float64_impl : Set :=
  | Float64NaN_ : float64_impl
  | Float64Bits_ : Z -> float64_impl.

Definition float32 := float32_impl.
Definition Float32NaN : float32 := Float32NaN_.
Definition float64 := float64_impl.
Definition Float64NaN : float64 := Float64NaN_.

Definition float32_canonical_nan_bits : Z := 2143289344.
Definition float64_canonical_nan_bits : Z := 9221120237041090560.

Definition raw_float32_zero := b32_of_bits 0.
Definition raw_float64_zero := b64_of_bits 0.

Definition raw_float32_of (f : float32) : raw_float32 :=
  match f with
  | Float32NaN_ => b32_of_bits float32_canonical_nan_bits
  | Float32Bits_ bits => b32_of_bits bits
  end.

Definition raw_float64_of (f : float64) : raw_float64 :=
  match f with
  | Float64NaN_ => b64_of_bits float64_canonical_nan_bits
  | Float64Bits_ bits => b64_of_bits bits
  end.

Definition raw_float32_is_nan (f : raw_float32) : bool := Binary.is_nan 24 128 f.
Definition raw_float64_is_nan (f : raw_float64) : bool := Binary.is_nan 53 1024 f.

Definition raw_float32_is_zero (f : raw_float32) : bool :=
  match b32_compare f raw_float32_zero with
  | Some Eq => true
  | _ => false
  end.

Definition raw_float64_is_zero (f : raw_float64) : bool :=
  match b64_compare f raw_float64_zero with
  | Some Eq => true
  | _ => false
  end.

Definition mk_float32 (f : raw_float32) : float32 :=
  if raw_float32_is_nan f then Float32NaN_
  else if raw_float32_is_zero f then Float32Bits_ 0
  else Float32Bits_ (bits_of_b32 f).

Definition mk_float64 (f : raw_float64) : float64 :=
  if raw_float64_is_nan f then Float64NaN_
  else if raw_float64_is_zero f then Float64Bits_ 0
  else Float64Bits_ (bits_of_b64 f).

Definition float32_is_nan (f : float32) : bool :=
  match f with Float32NaN_ => true | Float32Bits_ _ => false end.

Definition float64_is_nan (f : float64) : bool :=
  match f with Float64NaN_ => true | Float64Bits_ _ => false end.

Definition float32_is_infinite (f : float32) : bool :=
  andb (negb (float32_is_nan f))
       (negb (Binary.is_finite 24 128 (raw_float32_of f))).

Definition float64_is_infinite (f : float64) : bool :=
  andb (negb (float64_is_nan f))
       (negb (Binary.is_finite 53 1024 (raw_float64_of f))).

Definition float32_is_zero (f : float32) : bool :=
  raw_float32_is_zero (raw_float32_of f).

Definition float64_is_zero (f : float64) : bool :=
  raw_float64_is_zero (raw_float64_of f).

Lemma float32_is_nan_true_iff : forall value,
  float32_is_nan value = true <-> value = Float32NaN.
Proof.
intro value; destruct value; simpl; split; intro H;
  try discriminate; reflexivity.
Qed.

Lemma float64_is_nan_true_iff : forall value,
  float64_is_nan value = true <-> value = Float64NaN.
Proof.
intro value; destruct value; simpl; split; intro H;
  try discriminate; reflexivity.
Qed.

Lemma float32_is_nan_mk : forall raw,
  float32_is_nan (mk_float32 raw) = Binary.is_nan 24 128 raw.
Proof.
intro raw; unfold mk_float32, raw_float32_is_nan.
destruct (Binary.is_nan 24 128 raw); [reflexivity |].
now destruct (raw_float32_is_zero raw).
Qed.

Lemma float64_is_nan_mk : forall raw,
  float64_is_nan (mk_float64 raw) = Binary.is_nan 53 1024 raw.
Proof.
intro raw; unfold mk_float64, raw_float64_is_nan.
destruct (Binary.is_nan 53 1024 raw); [reflexivity |].
now destruct (raw_float64_is_zero raw).
Qed.

Lemma float32_is_infinite_nan :
  float32_is_infinite Float32NaN = false.
Proof. reflexivity. Qed.

Lemma float64_is_infinite_nan :
  float64_is_infinite Float64NaN = false.
Proof. reflexivity. Qed.

Definition float32_negative_sign_bit : Z := 2147483648.
Definition float64_negative_sign_bit : Z := 9223372036854775808.

Definition float32_order_key (f : float32) : Z * Z :=
  match f with
  | Float32NaN_ => (2, 0)
  | Float32Bits_ bits =>
      if float32_negative_sign_bit <=? bits
      then (0, - bits)
      else (1, bits)
  end.

Definition float64_order_key (f : float64) : Z * Z :=
  match f with
  | Float64NaN_ => (2, 0)
  | Float64Bits_ bits =>
      if float64_negative_sign_bit <=? bits
      then (0, - bits)
      else (1, bits)
  end.

Definition float32_compare_struct (f1 f2 : float32) :=
  compareAB Z.compare Z.compare (float32_order_key f1) (float32_order_key f2).

Definition float64_compare_struct (f1 f2 : float64) :=
  compareAB Z.compare Z.compare (float64_order_key f1) (float64_order_key f2).

Lemma float32_compare_struct_eq :
  forall f1 f2,
    match float32_compare_struct f1 f2 with
    | Eq => f1 = f2
    | _ => f1 <> f2
    end.
Proof.
intros [|bits1] [|bits2]; unfold float32_compare_struct, float32_order_key, compareAB; simpl.
- reflexivity.
- destruct (float32_negative_sign_bit <=? bits2); intro H; discriminate H.
- destruct (float32_negative_sign_bit <=? bits1); intro H; discriminate H.
- case_eq (float32_negative_sign_bit <=? bits1); intro Hs1;
  case_eq (float32_negative_sign_bit <=? bits2); intro Hs2; simpl.
  + case_eq (Z.compare (- bits1) (- bits2)); intro Hcmp.
    * apply f_equal. apply Z.compare_eq in Hcmp. lia.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
  + intro H; inversion H; subst. rewrite Hs1 in Hs2; discriminate.
  + intro H; inversion H; subst. rewrite Hs1 in Hs2; discriminate.
  + case_eq (Z.compare bits1 bits2); intro Hcmp.
    * apply f_equal. now apply Z.compare_eq.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
Qed.

Lemma float64_compare_struct_eq :
  forall f1 f2,
    match float64_compare_struct f1 f2 with
    | Eq => f1 = f2
    | _ => f1 <> f2
    end.
Proof.
intros [|bits1] [|bits2]; unfold float64_compare_struct, float64_order_key, compareAB; simpl.
- reflexivity.
- destruct (float64_negative_sign_bit <=? bits2); intro H; discriminate H.
- destruct (float64_negative_sign_bit <=? bits1); intro H; discriminate H.
- case_eq (float64_negative_sign_bit <=? bits1); intro Hs1;
  case_eq (float64_negative_sign_bit <=? bits2); intro Hs2; simpl.
  + case_eq (Z.compare (- bits1) (- bits2)); intro Hcmp.
    * apply f_equal. apply Z.compare_eq in Hcmp. lia.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
  + intro H; inversion H; subst. rewrite Hs1 in Hs2; discriminate.
  + intro H; inversion H; subst. rewrite Hs1 in Hs2; discriminate.
  + case_eq (Z.compare bits1 bits2); intro Hcmp.
    * apply f_equal. now apply Z.compare_eq.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
    * intro H; inversion H; subst.
      rewrite Z.compare_refl in Hcmp; discriminate.
Qed.

Definition Ofloat32 : Oset.Rcd float32.
Proof.
split with float32_compare_struct.
- apply float32_compare_struct_eq.
- unfold float32_compare_struct.
  intros a1 a2 a3.
  destruct (float32_order_key a1) as [c1 k1].
  destruct (float32_order_key a2) as [c2 k2].
  destruct (float32_order_key a3) as [c3 k3].
  eapply (@compareAB_lt_trans Z Z Z.compare Z.compare).
  + apply (Oset.compare_eq_trans OZ).
  + apply (Oset.compare_eq_lt_trans OZ).
  + apply (Oset.compare_lt_eq_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
- unfold float32_compare_struct.
  intros a1 a2.
  destruct (float32_order_key a1) as [c1 k1].
  destruct (float32_order_key a2) as [c2 k2].
  apply (@compareAB_lt_gt Z Z Z.compare Z.compare);
    [apply (Oset.compare_lt_gt OZ c1 c2) | apply (Oset.compare_lt_gt OZ k1 k2)].
Defined.

Definition Ofloat64 : Oset.Rcd float64.
Proof.
split with float64_compare_struct.
- apply float64_compare_struct_eq.
- unfold float64_compare_struct.
  intros a1 a2 a3.
  destruct (float64_order_key a1) as [c1 k1].
  destruct (float64_order_key a2) as [c2 k2].
  destruct (float64_order_key a3) as [c3 k3].
  eapply (@compareAB_lt_trans Z Z Z.compare Z.compare).
  + apply (Oset.compare_eq_trans OZ).
  + apply (Oset.compare_eq_lt_trans OZ).
  + apply (Oset.compare_lt_eq_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans OZ).
- unfold float64_compare_struct.
  intros a1 a2.
  destruct (float64_order_key a1) as [c1 k1].
  destruct (float64_order_key a2) as [c2 k2].
  apply (@compareAB_lt_gt Z Z Z.compare Z.compare);
    [apply (Oset.compare_lt_gt OZ c1 c2) | apply (Oset.compare_lt_gt OZ k1 k2)].
Defined.

(**
   PostgreSQL orders NaN after all non-NaN values and treats NaN as equal to
   NaN.  Non-NaN comparisons delegate to Flocq's IEEE comparison on the raw
   payload.  The wrapper canonicalization above ensures that SQL equality and
   FormalSQL's finite-set equality agree on NaN and signed zero.
*)
Definition float32_compare (f1 f2 : float32) : option comparison :=
  match f1, f2 with
  | Float32NaN_, Float32NaN_ => Some Eq
  | Float32NaN_, _ => Some Gt
  | _, Float32NaN_ => Some Lt
  | _, _ => b32_compare (raw_float32_of f1) (raw_float32_of f2)
  end.

Definition float64_compare (f1 f2 : float64) : option comparison :=
  match f1, f2 with
  | Float64NaN_, Float64NaN_ => Some Eq
  | Float64NaN_, _ => Some Gt
  | _, Float64NaN_ => Some Lt
  | _, _ => b64_compare (raw_float64_of f1) (raw_float64_of f2)
  end.

Lemma float32_compare_nan_left : forall value,
  float32_compare Float32NaN value =
    if float32_is_nan value then Some Eq else Some Gt.
Proof. now intros [|bits]. Qed.

Lemma float32_compare_nan_right : forall value,
  float32_compare value Float32NaN =
    if float32_is_nan value then Some Eq else Some Lt.
Proof. now intros [|bits]. Qed.

Lemma float64_compare_nan_left : forall value,
  float64_compare Float64NaN value =
    if float64_is_nan value then Some Eq else Some Gt.
Proof. now intros [|bits]. Qed.

Lemma float64_compare_nan_right : forall value,
  float64_compare value Float64NaN =
    if float64_is_nan value then Some Eq else Some Lt.
Proof. now intros [|bits]. Qed.

Definition float32_eqb f1 f2 :=
  match float32_compare f1 f2 with Some Eq => true | _ => false end.

Definition float64_eqb f1 f2 :=
  match float64_compare f1 f2 with Some Eq => true | _ => false end.

Definition float32_ltb f1 f2 :=
  match float32_compare f1 f2 with Some Lt => true | _ => false end.

Definition float64_ltb f1 f2 :=
  match float64_compare f1 f2 with Some Lt => true | _ => false end.

Definition float32_leb f1 f2 :=
  match float32_compare f1 f2 with
  | Some Lt | Some Eq => true
  | _ => false
  end.

Definition float64_leb f1 f2 :=
  match float64_compare f1 f2 with
  | Some Lt | Some Eq => true
  | _ => false
  end.

Definition lift_float32_unary f x :=
  mk_float32 (f (raw_float32_of x)).

Definition lift_float32_binary f x y :=
  mk_float32 (f (raw_float32_of x) (raw_float32_of y)).

Definition lift_float64_unary f x :=
  mk_float64 (f (raw_float64_of x)).

Definition lift_float64_binary f x y :=
  mk_float64 (f (raw_float64_of x) (raw_float64_of y)).

Definition float32_add := lift_float32_binary (b32_plus mode_NE).
Definition float32_sub := lift_float32_binary (b32_minus mode_NE).
Definition float32_mul := lift_float32_binary (b32_mult mode_NE).
Definition float32_div := lift_float32_binary (b32_div mode_NE).
Definition float32_opp := lift_float32_unary b32_opp.
Definition float32_zero := mk_float32 raw_float32_zero.
Lemma float32_prec_gt_0 : FLX.Prec_gt_0 24.
Proof. cbv; reflexivity. Qed.
Lemma float32_prec_lt_emax : Prec_lt_emax 24 128.
Proof. cbv; reflexivity. Qed.
Definition float32_of_Z z :=
  mk_float32
    (Binary.binary_normalize 24 128 float32_prec_gt_0 float32_prec_lt_emax
      mode_NE z 0 false).
Definition float32_max f1 f2 := if float32_ltb f1 f2 then f2 else f1.
Definition float32_min f1 f2 := if float32_ltb f1 f2 then f1 else f2.

Lemma float32_add_order_sensitive :
  exists first second third,
    float32_add (float32_add (float32_add float32_zero first) second) third <>
    float32_add (float32_add (float32_add float32_zero first) third) second.
Proof.
exists (mk_float32 (b32_of_bits 1266679808)).
exists (mk_float32 (b32_of_bits 1065353216)).
exists (mk_float32 (b32_of_bits 3414163456)).
vm_compute; discriminate.
Qed.

Definition float64_add := lift_float64_binary (b64_plus mode_NE).
Definition float64_sub := lift_float64_binary (b64_minus mode_NE).
Definition float64_mul := lift_float64_binary (b64_mult mode_NE).
Definition float64_div := lift_float64_binary (b64_div mode_NE).
Definition float64_opp := lift_float64_unary b64_opp.
Definition float64_zero := mk_float64 raw_float64_zero.
Lemma float64_prec_gt_0 : FLX.Prec_gt_0 53.
Proof. cbv; reflexivity. Qed.
Lemma float64_prec_lt_emax : Prec_lt_emax 53 1024.
Proof. cbv; reflexivity. Qed.
Definition float64_of_Z z :=
  mk_float64
    (Binary.binary_normalize 53 1024 float64_prec_gt_0 float64_prec_lt_emax
      mode_NE z 0 false).

(** PostgreSQL's [float4_accum] widens each REAL input exactly to float8
    before updating AVG's transition state.  Every finite binary32 value is
    exactly representable as binary64; normalization below performs that
    format conversion while preserving infinities and canonicalizing NaNs. *)
Definition float32_to_float64 (f : float32) : float64 :=
  match raw_float32_of f with
  | @Binary.B754_zero _ _ sign =>
      mk_float64 (@Binary.B754_zero 53 1024 sign)
  | @Binary.B754_infinity _ _ sign =>
      mk_float64 (@Binary.B754_infinity 53 1024 sign)
  | @Binary.B754_nan _ _ _ _ _ => Float64NaN
  | @Binary.B754_finite _ _ sign mantissa exponent _ =>
      mk_float64
        (Binary.binary_normalize 53 1024
          float64_prec_gt_0 float64_prec_lt_emax mode_NE
          (if sign then Z.neg mantissa else Z.pos mantissa)
          exponent sign)
  end.

Lemma float32_to_float64_nan :
  float32_to_float64 Float32NaN = Float64NaN.
Proof. vm_compute; reflexivity. Qed.

Definition float64_max f1 f2 := if float64_ltb f1 f2 then f2 else f1.
Definition float64_min f1 f2 := if float64_ltb f1 f2 then f1 else f2.

Lemma float32_average_order_sensitive :
  exists first second third,
    float64_div
      (float64_add
        (float64_add
          (float64_add float64_zero (float32_to_float64 first))
          (float32_to_float64 second))
        (float32_to_float64 third))
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)) <>
    float64_div
      (float64_add
        (float64_add
          (float64_add float64_zero (float32_to_float64 first))
          (float32_to_float64 third))
        (float32_to_float64 second))
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)).
Proof.
exists (mk_float32 (b32_of_bits 1904214016)).
exists (mk_float32 (b32_of_bits 1065353216)).
exists (mk_float32 (b32_of_bits 4051697664)).
vm_compute; discriminate.
Qed.

Lemma float64_add_order_sensitive :
  exists first second third,
    float64_add (float64_add (float64_add float64_zero first) second) third <>
    float64_add (float64_add (float64_add float64_zero first) third) second.
Proof.
exists (mk_float64 (b64_of_bits 4845873199050653696)).
exists (mk_float64 (b64_of_bits 4607182418800017408)).
exists (mk_float64 (b64_of_bits 14069245235905429504)).
vm_compute; discriminate.
Qed.

Lemma float64_average_order_sensitive :
  exists first second third,
    float64_div
      (float64_add (float64_add (float64_add float64_zero first) second) third)
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)) <>
    float64_div
      (float64_add (float64_add (float64_add float64_zero first) third) second)
      (float64_add
        (float64_add
          (float64_add float64_zero (float64_of_Z 1))
          (float64_of_Z 1))
        (float64_of_Z 1)).
Proof.
exists (mk_float64 (b64_of_bits 4845873199050653696)).
exists (mk_float64 (b64_of_bits 4607182418800017408)).
exists (mk_float64 (b64_of_bits 14069245235905429504)).
vm_compute; discriminate.
Qed.

End SqlFloat.

Export SqlFloat.
