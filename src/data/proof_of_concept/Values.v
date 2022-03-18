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
 | type_bool.

Open Scope N_scope.

Definition N_of_type := 
    fun d => 
    match d with   
    | type_string => 0
    | type_Z => 1
    | type_bool => 2
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
  | Value_bool : option bool -> value.

Register value as datacert.value.type.
Register Value_string as datacert.value.Value_string.
Register Value_Z as datacert.value.Value_Z.
Register Value_bool as datacert.value.Value_bool.

Definition type_of_value v := 
match v with
  | Value_string _  => type_string
  | Value_Z _ => type_Z
  | Value_bool _ => type_bool
  end.

(** Default values for each type. *)
Definition default_value d :=
  match d with
    | type_string => Value_string None
    | type_Z => Value_Z None
    | type_bool => Value_bool None
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
    | Value_string _, Value_bool _ => Lt

    | Value_Z _, Value_string _ => Gt
    | Value_Z z1, Value_Z z2 => option_compare _ Z.compare z1 z2
    | Value_Z _, Value_bool _ => Lt

    | Value_bool _, Value_string _
    | Value_bool _, Value_Z _ => Gt
    | Value_bool b1, Value_bool b2 => option_compare _ bool_compare b1 b2
  end.

Definition OVal : Oset.Rcd value.
split with value_compare.
- (* 1/3 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ]] [[s2 | ] | [z2 | ] | [b2 | ]];
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
- (* 1/2 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ]] [[s2 | ] | [z2 | ] | [b2 | ]] [[s3 | ] | [z3 | ] | [b3 | ]]; trivial; try discriminate; simpl.
  + apply (Oset.compare_lt_trans Ostring).
  + apply (Oset.compare_lt_trans OZ).
  + apply (Oset.compare_lt_trans Obool).
- (* 1/1 *)
  intros [[s1 | ] | [z1 | ] | [b1 | ]] [[s2 | ] | [z2 | ] | [b2 | ]]; trivial; simpl.
  + apply (Oset.compare_lt_gt Ostring).
  + apply (Oset.compare_lt_gt OZ).
  + apply (Oset.compare_lt_gt Obool).
Defined.

Definition FVal := Fset.build OVal.

Definition interp_predicate p :=
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Lt => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Gt => false3 | _ => true3 end
          | _ => unknown3
        end
    | Predicate ">" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Gt => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate ">=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Lt => false3 | _ => true3 end
          | _ => unknown3
        end
    | Predicate "=" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Eq => true3 | _ => false3 end
          | Value_string (Some s1) :: Value_string (Some s2) :: nil =>
            match string_compare s1 s2 with Eq => true3 | _ => false3 end
          | _ => unknown3
        end
    | Predicate "<>" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil =>
            match Z.compare a1 a2 with Eq => false3 | _ => true3 end
          | Value_string (Some s1) :: Value_string (Some s2) :: nil =>
            match string_compare s1 s2 with Eq => false3 | _ => true3 end
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
    | Symbol _ "mult" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zmult a1 a2))
          | _ => Value_Z None end
    | Symbol _ "minus" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: Value_Z (Some a2) :: nil => Value_Z (Some (Zminus a1 a2))
          | _ => Value_Z None end
    | Symbol _ "opp" =>
      fun l =>
        match l with
          | Value_Z (Some a1) :: nil => Value_Z (Some (Z.opp a1))
          | _ => Value_Z None end
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
    | Aggregate "count" => Value_Z (Some (Z_of_nat (List.length l)))
    | Aggregate "sum" =>
      Value_Z (Some (fold_left (fun acc x => match x with Value_Z (Some x) => (acc + x)%Z | _ => acc end) l 0%Z))
    | Aggregate "max" =>
      Value_Z (Some (
      if forallb
           (fun x =>
              match x with
              | Value_Z _ => true
              | _ => false
              end) l then
        let l' := filter
                   (fun x =>
                      match x with
                      | Value_Z (Some _) => true
                      | _ => false
                      end) l in
        match l' with
        | (Value_Z (Some z0)) :: l1 =>
          (fold_left (fun acc x => match x with 
                                          | Value_Z (Some x) => (Z.max acc x)%Z 
                                          | _ => acc end) l1 z0%Z)
        | _ =>  0%Z
        end
      else
         0%Z))
    | Aggregate "avg" =>
      Value_Z
        (Some (let sum :=
                   fold_left (fun acc x => match x with
                                           | Value_Z (Some x) => (acc + x)%Z
                                           | _ => acc end) l 0%Z in
               Z.quot sum (Z_of_nat (List.length l))))
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
