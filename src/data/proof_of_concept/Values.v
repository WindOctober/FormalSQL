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

Require Import Arith NArith ZArith String List Floats.
Require Import OrderedSet FiniteSet Bool3.

Definition float_lt := PrimFloat.ltb.
Definition float_le := PrimFloat.leb.
Definition float_eq_dec := PrimFloat.eqb.
Definition float_add := PrimFloat.add.
Definition float_mult := PrimFloat.mul.
Definition float_sub := PrimFloat.sub.
Definition float_div := PrimFloat.div.
Definition float_zero := PrimFloat.zero.
Definition float_of_int z := PrimFloat.of_uint63 (Uint63.of_Z z).
Definition float_max f1 f2 := if float_lt f1 f2 then f2 else f1.
Definition float_min f1 f2 := if float_lt f1 f2 then f1 else f2.

Module JsNumber.
  Definition neg_infinity := PrimFloat.neg_infinity.
End JsNumber.

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
 | type_float.

Open Scope N_scope.

Definition N_of_type := 
    fun d => 
    match d with   
    | type_string => 0
    | type_Z => 1
    | type_bool => 2
    | type_float => 3
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


Module NullValues.

(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : option string -> value
  | Value_Z : option Z -> value
  | Value_bool : option bool -> value
  | Value_float : option float -> value.

Register value as datacert.value.type.
Register Value_string as datacert.value.Value_string.
Register Value_Z as datacert.value.Value_Z.
Register Value_bool as datacert.value.Value_bool.
Register Value_float as datacert.value.Value_float.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  | Value_float _ => type_float
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string None
    | type_Z => Value_Z None
    | type_bool => Value_bool None
    | type_float => Value_float None
  end.

(** injection of domain names into natural numbers in order to
    build an ordering on them.
*)


(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
*)


Definition value_compare x y :=
  match x, y with
    | Value_string s1, Value_string s2 => option_compare _ string_compare s1 s2
    | Value_string _, Value_Z _
    | Value_string _, Value_bool _
    | Value_string _, Value_float _ => Lt

    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => option_compare _ Z.compare z1 z2
    | Value_Z _, Value_bool _
    | Value_Z _, Value_float _ => Lt

    | Value_bool _, Value_string _
    | Value_bool _, Value_Z _ => Gt
    | Value_bool b1, Value_bool b2 => option_compare _ bool_compare b1 b2
    | Value_bool _, Value_float _ => Lt

    | Value_float _, Value_string _
    | Value_float _, Value_Z _
    | Value_float _, Value_bool _ => Gt
    | Value_float f1, Value_float f2 => option_compare _ (Oset.compare Ofloat) f1 f2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ]];
    try discriminate; simpl; trivial.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
    * apply (f_equal (fun x => Value_string (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply (f_equal (fun x => Value_Z (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply (f_equal (fun x => Value_bool (Some x))).
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Ofloat f1 f2). change (Oset.compare Ofloat f1 f2) with (float_compare f1 f2). case (float_compare f1 f2).
    * intros ->; auto.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
- (* 1/2 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ]] [[s3 | ] | [z3 | ] | [b3 | ] | [f3 | ]]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
  + apply (Oset.compare_lt_trans Ofloat).
- (* 1/1 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ] | [f1 | ]] [[s2 | ] | [z2 | ] | [b2 | ] | [f2 | ]]; trivial; simpl.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
  + apply (Oset.compare_lt_gt Ofloat).
Defined.

Definition FVal := Fset.build OVal.

Definition is_null_value v :=
  match v with
  | Value_string None
  | Value_Z None
  | Value_bool None
  | Value_float None => true
  | _ => false
  end.

Definition same_non_null_value v1 v2 :=
  match v1, v2 with
  | Value_Z (Some a1), Value_Z (Some a2) =>
      match Z.compare a1 a2 with Eq => true | _ => false end
  | Value_float (Some a1), Value_float (Some a2) =>
      float_eq_dec a1 a2
  | Value_string (Some s1), Value_string (Some s2) =>
      match string_compare s1 s2 with Eq => true | _ => false end
  | Value_bool (Some b1), Value_bool (Some b2) =>
      Bool.eqb b1 b2
  | _, _ => false
  end.

Definition is_z_value v :=
  match v with
  | Value_Z _ => true
  | _ => false
  end.

Definition is_float_value v :=
  match v with
  | Value_float _ => true
  | _ => false
  end.

Fixpoint z_values l :=
  match l with
  | Value_Z (Some z) :: tl => z :: z_values tl
  | _ :: tl => z_values tl
  | nil => nil
  end.

Fixpoint float_values l :=
  match l with
  | Value_float (Some f) :: tl => f :: float_values tl
  | _ :: tl => float_values tl
  | nil => nil
  end.

Definition non_null_count l :=
  Z_of_nat (List.length (filter (fun v => negb (is_null_value v)) l)).

Definition interp_sum_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values => Value_Z (Some (fold_left Z.add values 0%Z))
    end
  else Value_Z None.

Definition interp_sum_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | values => Value_float (Some (fold_left float_add values float_zero))
    end
  else Value_float None.

Definition interp_max_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | z :: values => Value_Z (Some (fold_left Z.max values z))
    end
  else Value_Z None.

Definition interp_max_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | f :: values => Value_float (Some (fold_left float_max values f))
    end
  else Value_float None.

Definition interp_min_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | z :: values => Value_Z (Some (fold_left Z.min values z))
    end
  else Value_Z None.

Definition interp_min_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | f :: values => Value_float (Some (fold_left float_min values f))
    end
  else Value_float None.

Definition interp_avg_z l :=
  if forallb is_z_value l then
    match z_values l with
    | nil => Value_Z None
    | values =>
        let sum := fold_left Z.add values 0%Z in
        Value_Z (Some (Z.quot sum (Z_of_nat (List.length values))))
    end
  else Value_Z None.

Definition interp_avg_float l :=
  if forallb is_float_value l then
    match float_values l with
    | nil => Value_float None
    | values =>
        let sum := fold_left float_add values float_zero in
        let count := Z.of_nat (List.length values) in
        Value_float (Some (float_div sum (float_of_int count)))
    end
  else Value_float None.

Definition interp_predicate p :=
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Lt => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate "<." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_lt a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Gt => false3 | _ => true3 end
          | _ => unknown3
        end
    | Predicate "<=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_le a1 a2 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Gt => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate ">." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_lt a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate ">=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Lt => false3 | _ => true3 end
          | _ => unknown3
        end
    | Predicate ">=." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_le a2 a1 then true3 else false3
          | _ => unknown3
        end
    | Predicate "=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Eq => true3 | _ => false3 end
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_eq_dec a1 a2 then true3 else false3
          | Value_string (Some s1) :: Value_string (Some s2) :: nil =>
            match string_compare s1 s2 with Eq => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate "<>" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Eq => false3 | _ => true3 end
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            if float_eq_dec a1 a2 then false3 else true3
          | Value_string (Some s1) :: Value_string (Some s2) :: nil =>
            match string_compare s1 s2 with Eq => false3 | _ => true3 end
          | _ => unknown3
        end
    | Predicate "is_null" =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then true3 else false3
          | _ => unknown3
        end
    | Predicate "is_not_null" =>
      fun l =>
        match l with
          | v :: nil => if is_null_value v then false3 else true3
          | _ => unknown3
        end
    | Predicate "is_true" =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => true3
          | Value_bool (Some false) :: nil => false3
          | Value_bool None :: nil => unknown3
          | _ => unknown3
        end
    | Predicate "is_not_true" =>
      fun l =>
        match l with
          | Value_bool (Some true) :: nil => false3
          | Value_bool (Some false) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | Predicate "is_false" =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => true3
          | Value_bool (Some true) :: nil => false3
          | Value_bool None :: nil => unknown3
          | _ => unknown3
        end
    | Predicate "is_not_false" =>
      fun l =>
        match l with
          | Value_bool (Some false) :: nil => false3
          | Value_bool (Some true) :: nil
          | Value_bool None :: nil => true3
          | _ => unknown3
        end
    | Predicate "is_not_distinct_from" =>
      fun l =>
        match l with
          | v1 :: v2 :: nil =>
              if andb (is_null_value v1) (is_null_value v2)
              then true3
              else if orb (is_null_value v1) (is_null_value v2)
                   then false3
                   else if same_non_null_value v1 v2 then true3 else false3
          | _ => unknown3
        end
   | _ => fun _ => unknown3
  end.

Definition interp_symbol f :=
  match f with
    | Symbol _ "plus" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zplus a1 a2))
          | _ => Value_Z None end
    | Symbol _ "plus." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_add a1 a2))
          | _ => Value_float None end
    | Symbol _ "mult" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zmult a1 a2))
          | _ => Value_Z None end
    | Symbol _ "mult." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_mult a1 a2))
          | _ => Value_float None end
    | Symbol _ "minus" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zminus a1 a2))
          | _ => Value_Z None end
    | Symbol _ "minus." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: Value_float (Some a2) :: nil =>
            Value_float (Some (float_sub a1 a2))
          | _ => Value_float None end
    | Symbol _ "opp" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: nil => Value_Z (Some (Z.opp a1))
          | _ => Value_Z None end
    | Symbol _ "opp." =>
      fun l =>
        match l with
          | Value_float (Some a1) :: nil =>
            Value_float (Some (float_sub float_zero a1))
          | _ => Value_float None end
    | CstVal _ v =>
      fun l =>
        match l with
          | nil => v
          | _ => default_value (type_of_value v)
        end
    | _ => fun _ => Value_Z None
  end.

Definition interp_aggregate a l :=
  match a with
    | Aggregate "count" => Value_Z (Some (non_null_count l))
    | Aggregate "sum" => interp_sum_z l
    | Aggregate "sum." => interp_sum_float l
    | Aggregate "max" => interp_max_z l
    | Aggregate "max." => interp_max_float l
    | Aggregate "min" => interp_min_z l
    | Aggregate "min." => interp_min_float l
    | Aggregate "avg" => interp_avg_z l
    | Aggregate "avg." => interp_avg_float l
    | Aggregate _ => Value_Z None
  end.

End NullValues.
(*
(** Embedding several coq datatypes (corresponding to domains) into a single uniform
    type for values.
*)
Inductive value : Set :=
  | Value_string : string -> value
  | Value_Z : Z -> value
  | Value_bool : bool -> value.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string EmptyString
    | type_Z => Value_Z 0
    | type_bool => Value_bool false
  end.

(** injection of domain names into natural numbers in order to
    build an ordering on them.
*)

(** Comparison over values, in order to build an ordered type over values, and then
    finite sets.
*)
Definition value_compare x y := 
  match x, y with
    | Value_string s1, Value_string s2 => string_compare s1 s2
    | Value_string _, _ => Lt 
    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => Z.compare z1 z2
    | Value_Z _, _ => Lt
    | Value_bool _, Value_string _ => Gt
    | Value_bool _, Value_Z _ => Gt
    | Value_bool b1, Value_bool b2 => bool_compare b1 b2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2]; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl; case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok OZ z1 z2); simpl; case (Z.compare z1 z2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
  + generalize (Oset.eq_bool_ok Obool b1 b2); simpl; case (bool_compare b1 b2).
    * apply f_equal.
    * intros H1 H2; injection H2; apply H1.
    * intros H1 H2; injection H2; apply H1.
- (* 1/2 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2] [s3 | z3 | b3]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
- (* 1/1 *)
  intros [s1 | z1 | b1] [s2 | z2 | b2]; trivial; simpl.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
Defined.

Definition FVal := Fset.build OVal.
*)
