(************************************************************************************)
(** SQL integer domains used by Logos extensions.

    PostgreSQL INTEGER and BIGINT are signed fixed-width exact integer types.
    Arithmetic overflow is an error, not machine wraparound.  We model values as
    mathematical integers with range proofs and expose checked constructors and
    operations that return [None] on overflow.

    PostgreSQL reports overflow and division by zero as runtime errors, whereas
    the current proof-of-concept value domain has nullable values but no error
    monad.  Logos therefore uses these checked operations under the same
    no-runtime-error side condition used by the current proof pipeline: if an
    integer arithmetic operation would overflow or divide by zero, the generated
    proof obligation is outside this fragment until explicit SQL error semantics
    are added.
*)
(************************************************************************************)

Require Import ZArith.
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

Definition int64_add x y := int64_checked (int64_value x + int64_value y).
Definition int64_sub x y := int64_checked (int64_value x - int64_value y).
Definition int64_mul x y := int64_checked (int64_value x * int64_value y).
Definition int64_div x y :=
  if Z.eqb (int64_value y) 0
  then None
  else int64_checked (Z.quot (int64_value x) (int64_value y)).
Definition int64_opp x := int64_checked (- int64_value x).
