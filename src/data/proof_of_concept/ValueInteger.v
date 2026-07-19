(************************************************************************************)
(** SQL integer domains used by Logos extensions.

    PostgreSQL INTEGER and BIGINT are signed fixed-width exact integer types.
    Arithmetic overflow is an error, not machine wraparound.  We model values as
    mathematical integers with range proofs and expose checked constructors and
    operations that return [None] on overflow.

    The total value interpreter still returns [None] from a checked operation
    because values carry SQL NULL.  [SqlErrorSemantics] observes these checked
    operations separately and turns overflow or division by zero into a query-
    level [SqlError], so a runtime failure is never identified with SQL NULL.
*)
(************************************************************************************)

Require Import ZArith Lia.
Require Import OrderedSet.
Require Import Coq.Logic.ProofIrrelevance.

Open Scope Z_scope.

Definition int32_min : Z := (-2147483648)%Z.
Definition int32_max : Z := 2147483647%Z.
Definition int64_min : Z := (-9223372036854775808)%Z.
Definition int64_max : Z := 9223372036854775807%Z.

Record int32 : Set := Int32
  { int32_value : Z;
    int32_range : int32_min <= int32_value <= int32_max }.

Record int64 : Set := Int64
  { int64_value : Z;
    int64_range : int64_min <= int64_value <= int64_max }.

Lemma int32_ext : forall x y, int32_value x = int32_value y -> x = y.
Proof.
  intros [x Hx] [y Hy] H; simpl in H; subst.
  f_equal; apply proof_irrelevance.
Qed.

Lemma int64_ext : forall x y, int64_value x = int64_value y -> x = y.
Proof.
  intros [x Hx] [y Hy] H; simpl in H; subst.
  f_equal; apply proof_irrelevance.
Qed.

Definition int32_checked (z : Z) : option int32.
Proof.
  destruct (Z.leb_spec0 int32_min z) as [Hlo | Hlo].
  - destruct (Z.leb_spec0 z int32_max) as [Hhi | Hhi].
    + exact (Some (Int32 z (conj Hlo Hhi))).
    + exact None.
  - exact None.
Defined.

Definition int64_checked (z : Z) : option int64.
Proof.
  destruct (Z.leb_spec0 int64_min z) as [Hlo | Hlo].
  - destruct (Z.leb_spec0 z int64_max) as [Hhi | Hhi].
    + exact (Some (Int64 z (conj Hlo Hhi))).
    + exact None.
  - exact None.
Defined.

Lemma int64_checked_value : forall value,
  int64_checked (int64_value value) = Some value.
Proof.
intros [value [Hlo Hhi]].
unfold int64_checked.
cbn.
destruct (Z.leb_spec0 int64_min value) as [Hlo' | Hlo']; [|lia].
destruct (Z.leb_spec0 value int64_max) as [Hhi' | Hhi']; [|lia].
cbn.
f_equal; apply int64_ext; reflexivity.
Qed.

Lemma int32_value_in_int64_range : forall value,
  int64_min <= int32_value value <= int64_max.
Proof.
intros [integer Hrange].
cbn in *.
unfold int32_min, int32_max, int64_min, int64_max in *.
lia.
Qed.

(** PostgreSQL's [integer -> bigint] cast is an exact, total widening. *)
Definition int32_to_int64 (value : int32) : int64 :=
  Int64 (int32_value value) (int32_value_in_int64_range value).

Lemma int32_checked_outside_range : forall z,
  z < int32_min \/ int32_max < z -> int32_checked z = None.
Proof.
intros z Houtside.
unfold int32_checked.
destruct (Z.leb_spec0 int32_min z) as [Hlo | Hlo];
  [destruct (Z.leb_spec0 z int32_max) as [Hhi | Hhi] | ];
  try reflexivity; lia.
Qed.

Lemma int64_checked_outside_range : forall z,
  z < int64_min \/ int64_max < z -> int64_checked z = None.
Proof.
intros z Houtside.
unfold int64_checked.
destruct (Z.leb_spec0 int64_min z) as [Hlo | Hlo];
  [destruct (Z.leb_spec0 z int64_max) as [Hhi | Hhi] | ];
  try reflexivity; lia.
Qed.

(** Explicit decoding from an unbounded two's-complement bit pattern.  SQL
    literals and arithmetic must use the checked constructors instead; the
    bitwise operators below prove range closure and do not decode or wrap their
    mathematical results. *)
Definition int32_modulus : Z := 4294967296%Z.
Definition int64_modulus : Z := 18446744073709551616%Z.

Definition int32_from_twos_complement (z : Z) : int32.
Proof.
  refine (Int32
    (Z.modulo (z - int32_min) int32_modulus + int32_min) _).
  pose proof
    (Z.mod_pos_bound (z - int32_min) int32_modulus ltac:(
      unfold int32_modulus; lia)) as Hmod.
  unfold int32_modulus, int32_min, int32_max in *.
  lia.
Defined.

Definition int64_from_twos_complement (z : Z) : int64.
Proof.
  refine (Int64
    (Z.modulo (z - int64_min) int64_modulus + int64_min) _).
  pose proof
    (Z.mod_pos_bound (z - int64_min) int64_modulus ltac:(
      unfold int64_modulus; lia)) as Hmod.
  unfold int64_modulus, int64_min, int64_max in *.
  lia.
Defined.

(** If one operand of [Z.land] is nonnegative, the result is a nonnegative
    bitwise subset of that operand. *)
Local Lemma land_nonnegative_left_bounds : forall x y,
  0 <= x -> 0 <= Z.land x y <= x.
Proof.
  intros x y Hx; split.
  - apply (proj2 (Z.land_nonneg x y)); now left.
  - pose proof (Z.sub_land_same_l x y) as Hsplit.
    assert (0 <= Z.land x (Z.lnot y)) as Hother.
    { apply (proj2 (Z.land_nonneg x (Z.lnot y))); now left. }
    lia.
Qed.

Local Lemma log2_below_width : forall width z,
  0 < width -> 0 <= z < 2 ^ width -> Z.log2 z < width.
Proof.
  intros width z Hwidth [Hz Hbound].
  destruct (Z.eq_dec z 0) as [-> | Hnonzero].
  - cbn; lia.
  - apply (proj1 (Z.log2_lt_pow2 z width ltac:(lia))); exact Hbound.
Qed.

Local Lemma lor_nonnegative_below_pow2 : forall width x y,
  0 < width ->
  0 <= x < 2 ^ width ->
  0 <= y < 2 ^ width ->
  0 <= Z.lor x y < 2 ^ width.
Proof.
  intros width x y Hwidth Hx Hy.
  assert (Hnonnegative : 0 <= Z.lor x y).
  { apply (proj2 (Z.lor_nonneg x y)); lia. }
  split; [exact Hnonnegative|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [Hzero | Hnonzero].
  - rewrite Hzero; apply Z.pow_pos_nonneg; lia.
  - apply (proj2 (Z.log2_lt_pow2 (Z.lor x y) width ltac:(lia))).
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; now apply log2_below_width.
Qed.

(** [Z.land] and [Z.lor] use infinite two's-complement representations.  A
    fixed-width signed input has only its sign extension above [width], so both
    operations remain in the same signed interval. *)
Local Lemma signed_land_range : forall width x y,
  0 < width ->
  - (2 ^ width) <= x < 2 ^ width ->
  - (2 ^ width) <= y < 2 ^ width ->
  - (2 ^ width) <= Z.land x y < 2 ^ width.
Proof.
  intros width x y Hwidth Hx Hy.
  destruct (Z_le_gt_dec 0 x) as [Hxnonnegative | Hxnegative].
  - pose proof (land_nonnegative_left_bounds x y Hxnonnegative) as Hland.
    lia.
  - destruct (Z_le_gt_dec 0 y) as [Hynonnegative | Hynegative].
    + rewrite Z.land_comm.
      pose proof (land_nonnegative_left_bounds y x Hynonnegative) as Hland.
      lia.
    + assert (Hnotx : 0 <= Z.lnot x < 2 ^ width).
      { rewrite Z.lnot_eq_pred_opp; lia. }
      assert (Hnoty : 0 <= Z.lnot y < 2 ^ width).
      { rewrite Z.lnot_eq_pred_opp; lia. }
      pose proof (lor_nonnegative_below_pow2 width (Z.lnot x) (Z.lnot y)
        Hwidth Hnotx Hnoty) as Hlor.
      pose proof (Z.lnot_land x y) as Hdemorgan.
      rewrite Z.lnot_eq_pred_opp in Hdemorgan.
      lia.
Qed.

Local Lemma signed_lor_range : forall width x y,
  0 < width ->
  - (2 ^ width) <= x < 2 ^ width ->
  - (2 ^ width) <= y < 2 ^ width ->
  - (2 ^ width) <= Z.lor x y < 2 ^ width.
Proof.
  intros width x y Hwidth Hx Hy.
  destruct (Z_le_gt_dec 0 x) as [Hxnonnegative | Hxnegative].
  - destruct (Z_le_gt_dec 0 y) as [Hynonnegative | Hynegative].
    + pose proof (lor_nonnegative_below_pow2 width x y Hwidth
        (conj Hxnonnegative (proj2 Hx))
        (conj Hynonnegative (proj2 Hy))) as Hlor.
      lia.
    + assert (Hnoty : 0 <= Z.lnot y < 2 ^ width).
      { rewrite Z.lnot_eq_pred_opp; lia. }
      pose proof (land_nonnegative_left_bounds (Z.lnot y) (Z.lnot x)
        (proj1 Hnoty)) as Hland.
      rewrite Z.land_comm in Hland.
      pose proof (Z.lnot_lor x y) as Hdemorgan.
      rewrite Z.lnot_eq_pred_opp in Hdemorgan.
      lia.
  - assert (Hnotx : 0 <= Z.lnot x < 2 ^ width).
    { rewrite Z.lnot_eq_pred_opp; lia. }
    pose proof (land_nonnegative_left_bounds (Z.lnot x) (Z.lnot y)
      (proj1 Hnotx)) as Hland.
    pose proof (Z.lnot_lor x y) as Hdemorgan.
    rewrite Z.lnot_eq_pred_opp in Hdemorgan.
    lia.
Qed.

Lemma int32_land_in_range : forall x y : int32,
  int32_min <= Z.land (int32_value x) (int32_value y) <= int32_max.
Proof.
  intros x y.
  pose proof (int32_range x) as Hx.
  pose proof (int32_range y) as Hy.
  pose proof (signed_land_range 31 (int32_value x) (int32_value y)) as Hland.
  unfold int32_min, int32_max in *; cbn in Hland.
  specialize (Hland ltac:(lia) ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma int32_lor_in_range : forall x y : int32,
  int32_min <= Z.lor (int32_value x) (int32_value y) <= int32_max.
Proof.
  intros x y.
  pose proof (int32_range x) as Hx.
  pose proof (int32_range y) as Hy.
  pose proof (signed_lor_range 31 (int32_value x) (int32_value y)) as Hlor.
  unfold int32_min, int32_max in *; cbn in Hlor.
  specialize (Hlor ltac:(lia) ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma int64_land_in_range : forall x y : int64,
  int64_min <= Z.land (int64_value x) (int64_value y) <= int64_max.
Proof.
  intros x y.
  pose proof (int64_range x) as Hx.
  pose proof (int64_range y) as Hy.
  pose proof (signed_land_range 63 (int64_value x) (int64_value y)) as Hland.
  unfold int64_min, int64_max in *; cbn in Hland.
  specialize (Hland ltac:(lia) ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma int64_lor_in_range : forall x y : int64,
  int64_min <= Z.lor (int64_value x) (int64_value y) <= int64_max.
Proof.
  intros x y.
  pose proof (int64_range x) as Hx.
  pose proof (int64_range y) as Hy.
  pose proof (signed_lor_range 63 (int64_value x) (int64_value y)) as Hlor.
  unfold int64_min, int64_max in *; cbn in Hlor.
  specialize (Hlor ltac:(lia) ltac:(lia) ltac:(lia)); lia.
Qed.

(** PostgreSQL's integral bitwise aggregates use the ordinary two's-complement
    AND/OR operations of their signed transition type.  [Z.land]/[Z.lor]
    expose the same infinite two's-complement bit pattern.  Range closure is
    proved above, so no modulo normalization occurs on an SQL value. *)
Definition int32_bit_and (x y : int32) : int32 :=
  Int32 (Z.land (int32_value x) (int32_value y))
    (int32_land_in_range x y).
Definition int32_bit_or (x y : int32) : int32 :=
  Int32 (Z.lor (int32_value x) (int32_value y))
    (int32_lor_in_range x y).
Definition int64_bit_and (x y : int64) : int64 :=
  Int64 (Z.land (int64_value x) (int64_value y))
    (int64_land_in_range x y).
Definition int64_bit_or (x y : int64) : int64 :=
  Int64 (Z.lor (int64_value x) (int64_value y))
    (int64_lor_in_range x y).

Lemma int32_bit_and_value : forall x y,
  int32_value (int32_bit_and x y) = Z.land (int32_value x) (int32_value y).
Proof. reflexivity. Qed.

Lemma int32_bit_or_value : forall x y,
  int32_value (int32_bit_or x y) = Z.lor (int32_value x) (int32_value y).
Proof. reflexivity. Qed.

Lemma int64_bit_and_value : forall x y,
  int64_value (int64_bit_and x y) = Z.land (int64_value x) (int64_value y).
Proof. reflexivity. Qed.

Lemma int64_bit_or_value : forall x y,
  int64_value (int64_bit_or x y) = Z.lor (int64_value x) (int64_value y).
Proof. reflexivity. Qed.

Definition int32_compare x y := Oset.compare OZ (int32_value x) (int32_value y).
Definition int64_compare x y := Oset.compare OZ (int64_value x) (int64_value y).

Definition Oint32 : Oset.Rcd int32.
Proof.
  split with int32_compare.
  - intros x y; unfold int32_compare.
    generalize (Oset.eq_bool_ok OZ (int32_value x) (int32_value y)).
    case_eq (Oset.compare OZ (int32_value x) (int32_value y)); intro Hcmp; intro H.
    + apply int32_ext; exact H.
    + intro Hxy; inversion Hxy; subst.
      rewrite Oset.compare_eq_refl in Hcmp; discriminate.
    + intro Hxy; inversion Hxy; subst.
      rewrite Oset.compare_eq_refl in Hcmp; discriminate.
  - intros x y z; unfold int32_compare.
    apply (Oset.compare_lt_trans OZ).
  - intros x y; unfold int32_compare.
    apply (Oset.compare_lt_gt OZ).
Defined.

Definition Oint64 : Oset.Rcd int64.
Proof.
  split with int64_compare.
  - intros x y; unfold int64_compare.
    generalize (Oset.eq_bool_ok OZ (int64_value x) (int64_value y)).
    case_eq (Oset.compare OZ (int64_value x) (int64_value y)); intro Hcmp; intro H.
    + apply int64_ext; exact H.
    + intro Hxy; inversion Hxy; subst.
      rewrite Oset.compare_eq_refl in Hcmp; discriminate.
    + intro Hxy; inversion Hxy; subst.
      rewrite Oset.compare_eq_refl in Hcmp; discriminate.
  - intros x y z; unfold int64_compare.
    apply (Oset.compare_lt_trans OZ).
  - intros x y; unfold int64_compare.
    apply (Oset.compare_lt_gt OZ).
Defined.

Definition int32_add x y := int32_checked (int32_value x + int32_value y).
Definition int32_sub x y := int32_checked (int32_value x - int32_value y).
Definition int32_mul x y := int32_checked (int32_value x * int32_value y).
Definition int32_div x y :=
  if Z.eqb (int32_value y) 0
  then None
  else int32_checked (Z.quot (int32_value x) (int32_value y)).
Definition int32_opp x := int32_checked (- int32_value x).
