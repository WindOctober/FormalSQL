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

From Stdlib Require Import ZArith String List.
Require Import DecidableEquality.
Require Export ValueFloat.

Definition option_compare (A : Type) (c : A -> A -> comparison) x y :=
  match x, y with
  | Some x, Some y => c x y
  | Some _, None => Gt
  | None, Some _ => Lt
  | None, None => Eq
  end.

(** Types a.k.a domains in the database textbooks. *)
Inductive type := 
 | type_string 
 | type_Z
 | type_int32
 | type_int64
 | type_bool
 | type_float
 | type_double
 | type_numeric
 | type_date
 | type_time
 | type_timestamp
 | type_timestamptz.

(** The concrete model contains only predicates with an implemented PostgreSQL
    interpretation.  Keeping predicate names as arbitrary strings previously
    made misspellings and stale lowering output silently evaluate to UNKNOWN. *)
Inductive predicate : Type :=
  | PredicateLt
  | PredicateFloatLt
  | PredicateDoubleLt
  | PredicateDateLtTimestamp
  | PredicateDateLteTimestamp
  | PredicateDateGtTimestamp
  | PredicateDateGteTimestamp
  | PredicateLte
  | PredicateFloatLte
  | PredicateDoubleLte
  | PredicateGt
  | PredicateFloatGt
  | PredicateDoubleGt
  | PredicateGte
  | PredicateFloatGte
  | PredicateDoubleGte
  | PredicateEq
  | PredicateNeq
  | PredicateLikePrefix
  | PredicateLikePercent
  | PredicateIsNull
  | PredicateIsNotNull
  | PredicateIsTrue
  | PredicateIsNotTrue
  | PredicateIsFalse
  | PredicateIsNotFalse
  | PredicateIsNotDistinctFrom.

(** Arity is part of the closed predicate vocabulary.  Evaluators remain
    total on arbitrary lists, while query admissibility requires this exact
    arity before a predicate can enter the SQL semantics. *)
Definition predicate_arity predicate : nat :=
  match predicate with
  | PredicateIsNull
  | PredicateIsNotNull
  | PredicateIsTrue
  | PredicateIsNotTrue
  | PredicateIsFalse
  | PredicateIsNotFalse => 1
  | _ => 2
  end.

Register predicate_arity as datacert.predicate.arity.

Register predicate as datacert.predicate.type.
Register PredicateLt as datacert.predicate.PredicateLt.
Register PredicateFloatLt as datacert.predicate.PredicateFloatLt.
Register PredicateDoubleLt as datacert.predicate.PredicateDoubleLt.
Register PredicateDateLtTimestamp as datacert.predicate.PredicateDateLtTimestamp.
Register PredicateDateLteTimestamp as datacert.predicate.PredicateDateLteTimestamp.
Register PredicateDateGtTimestamp as datacert.predicate.PredicateDateGtTimestamp.
Register PredicateDateGteTimestamp as datacert.predicate.PredicateDateGteTimestamp.
Register PredicateLte as datacert.predicate.PredicateLte.
Register PredicateFloatLte as datacert.predicate.PredicateFloatLte.
Register PredicateDoubleLte as datacert.predicate.PredicateDoubleLte.
Register PredicateGt as datacert.predicate.PredicateGt.
Register PredicateFloatGt as datacert.predicate.PredicateFloatGt.
Register PredicateDoubleGt as datacert.predicate.PredicateDoubleGt.
Register PredicateGte as datacert.predicate.PredicateGte.
Register PredicateFloatGte as datacert.predicate.PredicateFloatGte.
Register PredicateDoubleGte as datacert.predicate.PredicateDoubleGte.
Register PredicateEq as datacert.predicate.PredicateEq.
Register PredicateNeq as datacert.predicate.PredicateNeq.
Register PredicateLikePrefix as datacert.predicate.PredicateLikePrefix.
Register PredicateLikePercent as datacert.predicate.PredicateLikePercent.
Register PredicateIsNull as datacert.predicate.PredicateIsNull.
Register PredicateIsNotNull as datacert.predicate.PredicateIsNotNull.
Register PredicateIsTrue as datacert.predicate.PredicateIsTrue.
Register PredicateIsNotTrue as datacert.predicate.PredicateIsNotTrue.
Register PredicateIsFalse as datacert.predicate.PredicateIsFalse.
Register PredicateIsNotFalse as datacert.predicate.PredicateIsNotFalse.
Register PredicateIsNotDistinctFrom as datacert.predicate.PredicateIsNotDistinctFrom.

(** Scalar operators return SQL values.  Predicates remain a distinct formula
    carrier and are lifted explicitly only when SQL observes their nullable
    BOOLEAN result in a value context such as SELECT or CASE. *)
Inductive scalar_numeric_kind : Type :=
  | ScalarInt32
  | ScalarInt64
  | ScalarFloat
  | ScalarDouble
  | ScalarNumeric.

Inductive scalar_boolean_operator : Type :=
  | ScalarAnd
  | ScalarOr
  | ScalarNot.

Inductive scalar_string_case : Type :=
  | ScalarUpper
  | ScalarLower.

Inductive scalar_date_part : Type :=
  | ScalarYear
  | ScalarMonth.

Inductive scalar_numeric_source : Type :=
  | ScalarSourceZ
  | ScalarSourceInt32
  | ScalarSourceInt64
  | ScalarSourceNumeric.

Inductive scalar_cast : Type :=
  | ScalarCastIdentity
  | ScalarCastToNumeric : scalar_numeric_source -> scalar_cast
  | ScalarCastToNumericTypmod : scalar_numeric_source -> scalar_cast
  | ScalarCastInt32ToDouble
  | ScalarCastInt32ToInt64
  | ScalarCastInt64ToInt32
  | ScalarCastNumericToInt32
  | ScalarCastDateToTimestamp
  | ScalarCastTimestampToDate
  | ScalarCastStringExplicit
  | ScalarCoerceStringImplicit.

Inductive scalar_timestamp_unit : Type :=
  | ScalarTimestampMicrosecond
  | ScalarTimestampSecond
  | ScalarTimestampMinute
  | ScalarTimestampHour
  | ScalarTimestampDay
  | ScalarTimestampMonth
  | ScalarTimestampYear.

Inductive scalar_operator : Type :=
  | ScalarPredicateValue : predicate -> scalar_operator
  | ScalarBoolean : scalar_boolean_operator -> scalar_operator
  | ScalarCase
  | ScalarStringCase : scalar_string_case -> scalar_operator
  | ScalarExtractDate : scalar_date_part -> scalar_operator
  | ScalarCast : scalar_cast -> scalar_operator
  | ScalarAdd : scalar_numeric_kind -> scalar_operator
  | ScalarSubtract : scalar_numeric_kind -> scalar_operator
  | ScalarMultiply : scalar_numeric_kind -> scalar_operator
  | ScalarDivide : scalar_numeric_kind -> scalar_operator
  | ScalarNegate : scalar_numeric_kind -> scalar_operator
  | ScalarNumericDivideResultScale
  | ScalarNumericDivideTypmod
  | ScalarPowerHalfInt64ToInt32
  | ScalarStringConcat
  | ScalarSubstringNonnegative
  | ScalarTimestampAdd : scalar_timestamp_unit -> scalar_operator.

Register scalar_operator as datacert.scalar.operator.type.

Definition scalar_operator_eq_dec : EqDec.t scalar_operator.
Proof.
unfold EqDec.t.
repeat decide equality.
Defined.

Inductive aggregate_quantifier : Type :=
  | AggregateAll
  | AggregateDistinct.

Register aggregate_quantifier as datacert.aggregate.quantifier.type.
Register AggregateAll as datacert.aggregate.quantifier.AggregateAll.
Register AggregateDistinct as datacert.aggregate.quantifier.AggregateDistinct.

(** Display scale is observable by later NUMERIC arithmetic even though it is
    intentionally absent from SQL numeric equality.  Keep that metadata as a
    structured observation of an ordinary aggregate instead of inventing a
    second SQL aggregate name or fusing a surrounding scalar expression. *)
Inductive numeric_aggregate : Type :=
  | NumericAverageInt32
  | NumericStddevSampleInt32.

Register numeric_aggregate as datacert.aggregate.numeric.type.
Register NumericAverageInt32 as datacert.aggregate.numeric.NumericAverageInt32.
Register NumericStddevSampleInt32 as datacert.aggregate.numeric.NumericStddevSampleInt32.

(** Aggregate functions are a closed semantic vocabulary.  Their structural
    equality is sufficient for syntax membership and permutation; evaluators
    never dispatch on strings. *)
Inductive aggregate_function : Type :=
  | AggregateCount
  | AggregateSumZ
  | AggregateSumInt32
  | AggregateSumInt64Numeric
  | AggregateSumFloat
  | AggregateSumDouble
  | AggregateSumNumeric
  | AggregateBitAndInt32
  | AggregateBitOrInt32
  | AggregateBitAndInt64
  | AggregateBitOrInt64
  | AggregateMaxZ
  | AggregateMaxInt32
  | AggregateMaxInt64
  | AggregateMaxFloat
  | AggregateMaxDouble
  | AggregateMaxNumeric
  | AggregateMaxString
  | AggregateMinZ
  | AggregateMinInt32
  | AggregateMinInt64
  | AggregateMinFloat
  | AggregateMinDouble
  | AggregateMinNumeric
  | AggregateSingleValueInt32
  | AggregateAverageZ
  | AggregateAverageInt32Numeric
  | AggregateNumericDisplayScale : numeric_aggregate -> aggregate_function
  | AggregateAverageInt64Numeric
  | AggregateVariancePopulationInt32
  | AggregateVarianceSampleInt32
  | AggregateStddevPopulationInt32
  | AggregateStddevSampleInt32
  | AggregateStddevSampleNumericFixed : Z -> Z -> aggregate_function
  | AggregateAverageFloat
  | AggregateAverageDouble
  | AggregateAverageNumericFixed : Z -> Z -> aggregate_function
  | AggregateAverageNumericAtScale : Z -> aggregate_function.

Register aggregate_function as datacert.aggregate.function.type.
Register AggregateCount as datacert.aggregate.function.AggregateCount.
Register AggregateSumZ as datacert.aggregate.function.AggregateSumZ.
Register AggregateSumInt32 as datacert.aggregate.function.AggregateSumInt32.
Register AggregateSumInt64Numeric as datacert.aggregate.function.AggregateSumInt64Numeric.
Register AggregateSumFloat as datacert.aggregate.function.AggregateSumFloat.
Register AggregateSumDouble as datacert.aggregate.function.AggregateSumDouble.
Register AggregateSumNumeric as datacert.aggregate.function.AggregateSumNumeric.
Register AggregateBitAndInt32 as datacert.aggregate.function.AggregateBitAndInt32.
Register AggregateBitOrInt32 as datacert.aggregate.function.AggregateBitOrInt32.
Register AggregateBitAndInt64 as datacert.aggregate.function.AggregateBitAndInt64.
Register AggregateBitOrInt64 as datacert.aggregate.function.AggregateBitOrInt64.
Register AggregateMaxZ as datacert.aggregate.function.AggregateMaxZ.
Register AggregateMaxInt32 as datacert.aggregate.function.AggregateMaxInt32.
Register AggregateMaxInt64 as datacert.aggregate.function.AggregateMaxInt64.
Register AggregateMaxFloat as datacert.aggregate.function.AggregateMaxFloat.
Register AggregateMaxDouble as datacert.aggregate.function.AggregateMaxDouble.
Register AggregateMaxNumeric as datacert.aggregate.function.AggregateMaxNumeric.
Register AggregateMaxString as datacert.aggregate.function.AggregateMaxString.
Register AggregateMinZ as datacert.aggregate.function.AggregateMinZ.
Register AggregateMinInt32 as datacert.aggregate.function.AggregateMinInt32.
Register AggregateMinInt64 as datacert.aggregate.function.AggregateMinInt64.
Register AggregateMinFloat as datacert.aggregate.function.AggregateMinFloat.
Register AggregateMinDouble as datacert.aggregate.function.AggregateMinDouble.
Register AggregateMinNumeric as datacert.aggregate.function.AggregateMinNumeric.
Register AggregateSingleValueInt32 as datacert.aggregate.function.AggregateSingleValueInt32.
Register AggregateAverageZ as datacert.aggregate.function.AggregateAverageZ.
Register AggregateAverageInt32Numeric as datacert.aggregate.function.AggregateAverageInt32Numeric.
Register AggregateNumericDisplayScale as datacert.aggregate.function.AggregateNumericDisplayScale.
Register AggregateAverageInt64Numeric as datacert.aggregate.function.AggregateAverageInt64Numeric.
Register AggregateVariancePopulationInt32 as datacert.aggregate.function.AggregateVariancePopulationInt32.
Register AggregateVarianceSampleInt32 as datacert.aggregate.function.AggregateVarianceSampleInt32.
Register AggregateStddevPopulationInt32 as datacert.aggregate.function.AggregateStddevPopulationInt32.
Register AggregateStddevSampleInt32 as datacert.aggregate.function.AggregateStddevSampleInt32.
Register AggregateStddevSampleNumericFixed as datacert.aggregate.function.AggregateStddevSampleNumericFixed.
Register AggregateAverageFloat as datacert.aggregate.function.AggregateAverageFloat.
Register AggregateAverageDouble as datacert.aggregate.function.AggregateAverageDouble.
Register AggregateAverageNumericFixed as datacert.aggregate.function.AggregateAverageNumericFixed.
Register AggregateAverageNumericAtScale as datacert.aggregate.function.AggregateAverageNumericAtScale.

(** SQL's ALL/DISTINCT set quantifier belongs only to ordinary one-argument
    aggregate calls.  COUNT-star has no argument and therefore has a dedicated
    constructor: the invalid DISTINCT count-star shape is uninhabitable. *)
Inductive aggregate : Type :=
  | AggregateCall : aggregate_function -> aggregate_quantifier -> aggregate
  | AggregateCountStar.

Register aggregate as datacert.aggregate.type.
Register AggregateCall as datacert.aggregate.AggregateCall.
Register AggregateCountStar as datacert.aggregate.AggregateCountStar.

Definition Aggregate function := AggregateCall function AggregateAll.
Definition DistinctAggregate function := AggregateCall function AggregateDistinct.

Definition aggregate_eq_dec : EqDec.t aggregate.
Proof.
unfold EqDec.t.
repeat decide equality.
Defined.
