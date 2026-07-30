(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                    Observable outcomes of SQL evaluation                        *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

(**
  Query failures are observable SQL behavior, not SQL values.  In particular,
  [SqlError] must never be represented by NULL, an empty relation, or an arbitrary
  default value.

  The carrier includes failures PostgreSQL reports while analyzing a query, such as
  an undefined operator/function, as well as failures raised while executing a
  successfully analyzed expression.  It intentionally excludes SQL parse failures,
  malformed Logos IR, and unsupported lowering: those indicate that no FormalSQL
  term was produced and therefore are not semantic outcomes of a query expression.
 *)
(** SQLSTATE class 22 (data exception), at the granularity observed by Logos. *)
Inductive sql_data_exception : Type :=
  | DivisionByZero
  | NumericValueOutOfRange
  | StringDataRightTruncation
  | InvalidTextRepresentation
  | InvalidDatetimeFormat
  | DatetimeFieldOverflow
  | InvalidParameterValue
  (** SQLSTATE 2201F, used by PostgreSQL for a negative base raised to a
      non-integral power. *)
  | InvalidArgumentForPowerFunction.

(** [CardinalityViolation] corresponds to SQLSTATE class 21,
    [AmbiguousColumn] to SQLSTATE 42702, [UndefinedColumn] to SQLSTATE 42703,
    [UndefinedFunction] to SQLSTATE 42883, and
    [FeatureNotSupported] to SQLSTATE class 0A.  PostgreSQL uses the latter
    for casts from NUMERIC NaN or infinity to an integer type. *)
Inductive sql_runtime_error : Type :=
  | CardinalityViolation
  | FeatureNotSupported
  | AmbiguousColumn
  | UndefinedColumn
  | UndefinedFunction
  | DataException : sql_data_exception -> sql_runtime_error.

Inductive sql_outcome (A : Type) : Type :=
  | SqlSuccess : A -> sql_outcome A
  | SqlError : sql_runtime_error -> sql_outcome A.

Arguments SqlSuccess {A} _.
Arguments SqlError {A} _.

(**
  Two deterministic evaluations are equivalent only when both terminate
  successfully and their values satisfy [value_equiv].  Even two occurrences of
  the same runtime error are deliberately not equivalent: Logos proves equality of
  successful query results, rather than equivalence of failing executions.
 *)
Definition successful_outcome_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A) : Prop :=
  match left, right with
  | SqlSuccess left_value, SqlSuccess right_value =>
      value_equiv left_value right_value
  | _, _ => False
  end.

(** Error-preserving equivalence compares every observable SQL outcome.  A
    successful evaluation must still satisfy [value_equiv], while failures are
    equivalent exactly when PostgreSQL exposes the same error category. *)
Definition outcome_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A) : Prop :=
  match left, right with
  | SqlSuccess left_value, SqlSuccess right_value =>
      value_equiv left_value right_value
  | SqlError left_error, SqlError right_error =>
      left_error = right_error
  | _, _ => False
  end.

(**
  Relational evaluators, such as the ordered-observation semantics, may have
  several successful outputs.  Equivalence requires at least one successful
  left output, excludes every error outcome on both sides, and matches successful
  outputs in both directions through [value_equiv].  The explicit relation is
  essential for represented SQL values: observable equality need not coincide
  with Coq's Leibniz equality on their internal representation.
 *)
Definition successful_relation_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) : Prop :=
  (exists value, left (SqlSuccess value)) /\
  (forall error, ~ left (SqlError error)) /\
  (forall error, ~ right (SqlError error)) /\
  (forall left_value,
    left (SqlSuccess left_value) ->
    exists right_value,
      right (SqlSuccess right_value) /\ value_equiv left_value right_value) /\
  (forall right_value,
    right (SqlSuccess right_value) ->
    exists left_value,
      left (SqlSuccess left_value) /\ value_equiv left_value right_value).

(** Relational evaluators can expose several legal successes or errors.  The
    lifting below requires both relations to expose at least one outcome and
    then compares all of them: successful observations are matched in both
    directions through [value_equiv], and the set of error categories is
    identical.  The nonemptiness clauses prevent two undefined or incomplete
    evaluator relations from becoming vacuously equivalent.  The definition
    therefore remains exact for nondeterministic ordered SQL observations
    rather than selecting one execution. *)
Definition outcome_relation_equiv {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) : Prop :=
  (exists left_outcome, left left_outcome) /\
  (exists right_outcome, right right_outcome) /\
  (forall left_value,
    left (SqlSuccess left_value) ->
    exists right_value,
      right (SqlSuccess right_value) /\ value_equiv left_value right_value) /\
  (forall right_value,
    right (SqlSuccess right_value) ->
    exists left_value,
      left (SqlSuccess left_value) /\ value_equiv left_value right_value) /\
  (forall error, left (SqlError error) <-> right (SqlError error)).

(** A relational evaluator has a unique successful observation modulo the
    supplied semantic equality when every two successes are equivalent.  The
    definition intentionally says nothing about errors: functionality is a
    certificate about the successful observation set, not a safety claim. *)
Definition successful_relation_functional {A : Type}
    (value_equiv : A -> A -> Prop)
    (outcomes : sql_outcome A -> Prop) : Prop :=
  forall left_value right_value,
    outcomes (SqlSuccess left_value) ->
    outcomes (SqlSuccess right_value) ->
    value_equiv left_value right_value.

(** A countermodel for relational observations must distinguish one legal
    outcome from *every* outcome on the opposite side.  The four constructors
    record the direction and whether the witness is a success or an error.
    They therefore cover sequence-valued observations and runtime failures
    without selecting an arbitrary representative from either relation. *)
Inductive outcome_relation_separation {A : Type}
    (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop) : Prop :=
  | OutcomeSeparationLeftSuccess :
      forall left_value,
        left (SqlSuccess left_value) ->
        (forall right_value,
          right (SqlSuccess right_value) ->
          ~ value_equiv left_value right_value) ->
        outcome_relation_separation value_equiv left right
  | OutcomeSeparationRightSuccess :
      forall right_value,
        right (SqlSuccess right_value) ->
        (forall left_value,
          left (SqlSuccess left_value) ->
          ~ value_equiv left_value right_value) ->
        outcome_relation_separation value_equiv left right
  | OutcomeSeparationLeftError :
      forall error,
        left (SqlError error) ->
        ~ right (SqlError error) ->
        outcome_relation_separation value_equiv left right
  | OutcomeSeparationRightError :
      forall error,
        right (SqlError error) ->
        ~ left (SqlError error) ->
        outcome_relation_separation value_equiv left right.

(** Directional separation is a kernel-checkable refutation of complete
    outcome-relation equivalence. *)
Lemma outcome_relation_separation_sound :
  forall (A : Type) (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop),
    outcome_relation_separation value_equiv left right ->
    ~ outcome_relation_equiv value_equiv left right.
Proof.
intros A value_equiv left right Hseparation
  [_ [_ [Hforward [Hbackward Herrors]]]].
destruct Hseparation as
  [left_value Hleft Hseparate
  | right_value Hright Hseparate
  | error Hleft Hseparate
  | error Hright Hseparate].
- destruct (Hforward left_value Hleft)
    as [right_value [Hright Hequivalent]].
  exact (Hseparate right_value Hright Hequivalent).
- destruct (Hbackward right_value Hright)
    as [left_value [Hleft Hequivalent]].
  exact (Hseparate left_value Hleft Hequivalent).
- apply Hseparate.
  now apply (proj1 (Herrors error)).
- apply Hseparate.
  now apply (proj2 (Herrors error)).
Qed.

Lemma outcome_equiv_refl :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall value, value_equiv value value) ->
    forall outcome, outcome_equiv value_equiv outcome outcome.
Proof.
intros A value_equiv Hrefl [value | error]; simpl; auto.
Qed.

Lemma outcome_relation_equiv_refl :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall value, value_equiv value value) ->
    forall outcomes,
      (exists outcome, outcomes outcome) ->
      outcome_relation_equiv value_equiv outcomes outcomes.
Proof.
intros A value_equiv Hrefl outcomes Houtcome.
unfold outcome_relation_equiv.
split; [exact Houtcome |].
split; [exact Houtcome |].
split.
- intros value Hvalue; exists value; auto.
- split.
  + intros value Hvalue; exists value; auto.
  + intros observed_error; tauto.
Qed.

Lemma successful_relation_equiv_refl :
  forall (A : Type) (value_equiv : A -> A -> Prop),
    (forall value, value_equiv value value) ->
    forall outcomes,
      (exists value, outcomes (SqlSuccess value)) ->
      (forall error, ~ outcomes (SqlError error)) ->
      successful_relation_equiv value_equiv outcomes outcomes.
Proof.
intros A value_equiv Hrefl outcomes Hsuccess Hsafe.
unfold successful_relation_equiv.
repeat split; try assumption.
- intros left_value Hleft.
  exists left_value; now split.
- intros right_value Hright.
  exists right_value; now split.
Qed.

Lemma outcome_relation_equiv_intro :
  forall (A : Type) (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop),
    (exists outcome, left outcome) ->
    (exists outcome, right outcome) ->
    (forall left_value,
      left (SqlSuccess left_value) ->
      exists right_value,
        right (SqlSuccess right_value) /\ value_equiv left_value right_value) ->
    (forall right_value,
      right (SqlSuccess right_value) ->
      exists left_value,
        left (SqlSuccess left_value) /\ value_equiv left_value right_value) ->
    (forall error, left (SqlError error) <-> right (SqlError error)) ->
    outcome_relation_equiv value_equiv left right.
Proof.
intros A value_equiv left right Hleft Hright Hforward Hbackward Herrors.
unfold outcome_relation_equiv.
split; [exact Hleft |].
split; [exact Hright |].
split; [exact Hforward |].
split; [exact Hbackward | exact Herrors].
Qed.

Lemma successful_outcome_equiv_success :
  forall (A : Type) (value_equiv : A -> A -> Prop) left right,
    successful_outcome_equiv value_equiv (SqlSuccess left) (SqlSuccess right) <->
    value_equiv left right.
Proof.
intros; split; trivial.
Qed.

Lemma successful_outcome_equiv_left_error :
  forall (A : Type) (value_equiv : A -> A -> Prop) error right,
    ~ successful_outcome_equiv value_equiv (@SqlError A error) right.
Proof.
intros A value_equiv error [right | right] H; exact H.
Qed.

Lemma successful_outcome_equiv_right_error :
  forall (A : Type) (value_equiv : A -> A -> Prop) left error,
    ~ successful_outcome_equiv value_equiv left (@SqlError A error).
Proof.
intros A value_equiv [left | left] error H; exact H.
Qed.

Lemma successful_outcome_equiv_errors :
  forall (A : Type) (value_equiv : A -> A -> Prop) left_error right_error,
    ~ successful_outcome_equiv value_equiv
        (@SqlError A left_error) (@SqlError A right_error).
Proof.
intros A value_equiv left_error right_error H; exact H.
Qed.

Lemma successful_relation_equiv_intro :
  forall (A : Type) (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop),
    (exists value, left (SqlSuccess value)) ->
    (forall error, ~ left (SqlError error)) ->
    (forall error, ~ right (SqlError error)) ->
    (forall left_value,
      left (SqlSuccess left_value) ->
      exists right_value,
        right (SqlSuccess right_value) /\ value_equiv left_value right_value) ->
    (forall right_value,
      right (SqlSuccess right_value) ->
      exists left_value,
        left (SqlSuccess left_value) /\ value_equiv left_value right_value) ->
    successful_relation_equiv value_equiv left right.
Proof.
intros A value_equiv left right Hsuccess Hleft Hright Hforward Hbackward.
unfold successful_relation_equiv.
split; [exact Hsuccess |].
split; [exact Hleft |].
split; [exact Hright |].
split; [exact Hforward | exact Hbackward].
Qed.

Lemma successful_relation_equiv_has_right_success :
  forall (A : Type) (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop),
    successful_relation_equiv value_equiv left right ->
    exists value, right (SqlSuccess value).
Proof.
intros A value_equiv left right
  [[left_value Hleft] [_ [_ [Hforward _]]]].
destruct (Hforward left_value Hleft) as [right_value [Hright _]].
now exists right_value.
Qed.

(** A safe equivalence is a stronger certificate than error-preserving
    equivalence.  Proof search may establish the former and lift it to the
    latter without any external safety classification. *)
Lemma successful_relation_equiv_implies_outcome_relation_equiv :
  forall (A : Type) (value_equiv : A -> A -> Prop)
    (left right : sql_outcome A -> Prop),
    successful_relation_equiv value_equiv left right ->
    outcome_relation_equiv value_equiv left right.
Proof.
intros A value_equiv left right
  [Hleft_success [Hleft_safe [Hright_safe [Hforward Hbackward]]]].
apply outcome_relation_equiv_intro.
- destruct Hleft_success as [value Hvalue].
  now exists (SqlSuccess value).
- destruct Hleft_success as [left_value Hleft].
  destruct (Hforward left_value Hleft) as [right_value [Hright _]].
  now exists (SqlSuccess right_value).
- exact Hforward.
- exact Hbackward.
- intro error; split; intro Herror.
  + contradiction (Hleft_safe error Herror).
  + contradiction (Hright_safe error Herror).
Qed.
