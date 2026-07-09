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

Require Import Arith NArith ZArith String List.
Require Import OrderedSet FiniteSet Bool3.
Require Export ValueFloat.

Definition option_compare (A : Type) (c : A -> A -> comparison) x y :=
  match x, y with
  | Some x, Some y => c x y
  | Some _, None => Gt
  | None, Some _ => Lt
  | None, None => Eq
  end.

Section Sec.

Hypothesis value : Type.
Hypothesis OVal : Oset.Rcd value.

(** Types a.k.a domains in the database textbooks. *)
Inductive type := 
 | type_string 
 | type_Z
 | type_bool
 | type_float
 | type_double
 | type_decimal
 | type_date
 | type_timestamp
 | type_timestamptz.

Open Scope N_scope.

Definition N_of_type := 
    fun d => 
    match d with   
    | type_string => 0
    | type_Z => 1
    | type_bool => 2
    | type_float => 3
    | type_double => 4
    | type_decimal => 5
    | type_date => 6
    | type_timestamp => 7
    | type_timestamptz => 8
    end.

Definition OT : Oset.Rcd type.
apply Oemb with N_of_type.
intros d1 d2; case d1; case d2;
(exact (fun _ => refl_equal _) || (intro Abs; discriminate Abs)).
Defined.

Inductive predicate : Type := Predicate : string -> predicate.

Register predicate as datacert.predicate.type.
Register Predicate as datacert.predicate.Predicate.

Definition OP : Oset.Rcd predicate.
split with (fun x y => match x, y with Predicate s1, Predicate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Inductive symbol : Type :=
  | Symbol : string -> symbol
  | CstVal : value -> symbol.

Definition symbol_compare (s1 s2 : symbol) :=
  match s1, s2 with
    | Symbol s1, Symbol s2 => string_compare s1 s2
    | Symbol _, CstVal _ => Lt
    | CstVal _, Symbol _ => Gt
    | CstVal v1, CstVal v2 => Oset.compare OVal v1 v2
  end.

Definition OSymbol : Oset.Rcd symbol.
split with symbol_compare.
- intros [s1 | s1] [s2 | s2]; simpl; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
    case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + generalize (Oset.eq_bool_ok OVal s1 s2); simpl.
    case (Oset.compare OVal s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1 | s1] [s2 | s2] [s3 | s3]; simpl;
  try (apply (Oset.compare_lt_trans Ostring) ||
             apply (Oset.compare_lt_trans OVal) ||
             trivial || discriminate).
- intros [s1 | s1] [s2 | s2]; simpl;
  try (apply (Oset.compare_lt_gt Ostring) ||
             apply (Oset.compare_lt_gt OVal) ||
             trivial || discriminate).
Defined.

Inductive aggregate : Type :=
  | Aggregate : string -> aggregate.

Definition OAgg : Oset.Rcd aggregate.
split with (fun x y => match x, y with Aggregate s1, Aggregate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

End Sec.
