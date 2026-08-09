(************************************************************************************)
(** PostgreSQL text input syntax for INTEGER and BIGINT. *)
(************************************************************************************)

From Stdlib Require Import ZArith String Ascii Bool.
Require Export ValueInteger ValueString.

Open Scope Z_scope.

(** PostgreSQL distinguishes malformed input from a syntactically valid integer
    whose magnitude is outside the destination domain. *)
Inductive text_integer_result (A : Type) : Type :=
  | TextIntegerValue : A -> text_integer_result A
  | TextIntegerInvalid
  | TextIntegerOutOfRange.

Arguments TextIntegerValue {A} _.
Arguments TextIntegerInvalid {A}.
Arguments TextIntegerOutOfRange {A}.

Inductive integer_magnitude_scan : Type :=
  | MagnitudeDone (value : Z) (rest : string) (saw_digit : bool)
  | MagnitudeInvalid
  | MagnitudeOutOfRange.

Definition ascii_code (character : ascii) : Z :=
  Z.of_nat (nat_of_ascii character).

Definition ascii_eq_code (character : ascii) (code : nat) : bool :=
  Ascii.eqb character (Ascii.ascii_of_nat code).

(** This is the ASCII whitespace class consumed by PostgreSQL's numutils.c. *)
Definition ascii_is_integer_space (character : ascii) : bool :=
  let code := ascii_code character in
  ((9 <=? code) && (code <=? 13)) || (code =? 32).

Fixpoint drop_integer_leading_spaces (input : string) : string :=
  match input with
  | EmptyString => EmptyString
  | String character rest =>
      if ascii_is_integer_space character
      then drop_integer_leading_spaces rest
      else input
  end.

Fixpoint string_all_integer_spaces (input : string) : bool :=
  match input with
  | EmptyString => true
  | String character rest =>
      ascii_is_integer_space character && string_all_integer_spaces rest
  end.

Definition ascii_integer_digit (base : Z) (character : ascii) : option Z :=
  let code := ascii_code character in
  let decimal := code - 48 in
  if (0 <=? decimal) && (decimal <? Z.min base 10)
  then Some decimal
  else if (10 <? base) && (65 <=? code) && (code <=? 70)
       then Some (code - 55)
       else if (10 <? base) && (97 <=? code) && (code <=? 102)
            then Some (code - 87)
            else None.

(** The accumulator follows pg_strtoint32_safe/pg_strtoint64_safe: it uses the
    absolute value of the most negative destination value as its limit.  The
    pre-multiplication test intentionally happens before inspecting later input,
    preserving PostgreSQL's overflow-versus-invalid-syntax error precedence. *)
Fixpoint scan_integer_magnitude
    (base overflow_threshold accumulator : Z)
    (allow_initial_underscore : bool)
    (saw_digit : bool)
    (input : string) : integer_magnitude_scan :=
  match input with
  | EmptyString => MagnitudeDone accumulator EmptyString saw_digit
  | String character rest =>
      match ascii_integer_digit base character with
      | Some digit =>
          if overflow_threshold <? accumulator
          then MagnitudeOutOfRange
          else scan_integer_magnitude base overflow_threshold
                 (accumulator * base + digit) allow_initial_underscore true rest
      | None =>
          if ascii_eq_code character 95
          then
            if saw_digit || allow_initial_underscore
            then
              match rest with
              | String next _ =>
                  match ascii_integer_digit base next with
                  | Some _ =>
                      scan_integer_magnitude base overflow_threshold
                        accumulator allow_initial_underscore saw_digit rest
                  | None => MagnitudeInvalid
                  end
              | EmptyString => MagnitudeInvalid
              end
            else MagnitudeInvalid
          else MagnitudeDone accumulator input saw_digit
      end
  end.

Definition integer_sign_and_body (input : string) : bool * string :=
  match drop_integer_leading_spaces input with
  | String character rest =>
      if ascii_eq_code character 45 then (true, rest)
      else if ascii_eq_code character 43 then (false, rest)
      else (false, String character rest)
  | EmptyString => (false, EmptyString)
  end.

Definition integer_base_and_digits (input : string) : Z * bool * string :=
  match input with
  | String zero (String prefix rest) =>
      if ascii_eq_code zero 48
      then
        if ascii_eq_code prefix 120 || ascii_eq_code prefix 88
        then (16, true, rest)
        else if ascii_eq_code prefix 111 || ascii_eq_code prefix 79
             then (8, true, rest)
             else if ascii_eq_code prefix 98 || ascii_eq_code prefix 66
                  then (2, true, rest)
                  else (10, false, input)
      else (10, false, input)
  | _ => (10, false, input)
  end.

Definition parse_text_integer_magnitude
    (minimum maximum : Z) (input : string) : text_integer_result Z :=
  let '(negative, signed_body) := integer_sign_and_body input in
  let '(base, allow_initial_underscore, digits) :=
    integer_base_and_digits signed_body in
  let absolute_minimum := - minimum in
  match scan_integer_magnitude
          base (absolute_minimum / base) 0 allow_initial_underscore false digits with
  | MagnitudeInvalid => TextIntegerInvalid
  | MagnitudeOutOfRange => TextIntegerOutOfRange
  | MagnitudeDone magnitude rest saw_digit =>
      if negb saw_digit || negb (string_all_integer_spaces rest)
      then TextIntegerInvalid
      else if negative
           then if magnitude <=? absolute_minimum
                then TextIntegerValue (- magnitude)
                else TextIntegerOutOfRange
           else if magnitude <=? maximum
                then TextIntegerValue magnitude
                else TextIntegerOutOfRange
  end.

Definition parse_text_int32 (input : string) : text_integer_result int32 :=
  match parse_text_integer_magnitude int32_min int32_max input with
  | TextIntegerValue value =>
      match int32_checked value with
      | Some result => TextIntegerValue result
      | None => TextIntegerOutOfRange
      end
  | TextIntegerInvalid => TextIntegerInvalid
  | TextIntegerOutOfRange => TextIntegerOutOfRange
  end.

Definition parse_text_int64 (input : string) : text_integer_result int64 :=
  match parse_text_integer_magnitude int64_min int64_max input with
  | TextIntegerValue value =>
      match int64_checked value with
      | Some result => TextIntegerValue result
      | None => TextIntegerOutOfRange
      end
  | TextIntegerInvalid => TextIntegerInvalid
  | TextIntegerOutOfRange => TextIntegerOutOfRange
  end.

(** Successful typed parsing factors through the generic magnitude parser and
    the checked destination constructor.  These decomposition laws preserve
    both the parsed mathematical integer and the fixed-width range check. *)
Lemma parse_text_int32_value_iff : forall input result,
  parse_text_int32 input = TextIntegerValue result <->
  exists integer,
    parse_text_integer_magnitude int32_min int32_max input =
      TextIntegerValue integer /\
    int32_checked integer = Some result.
Proof.
  intros input result; split.
  - unfold parse_text_int32.
    destruct (parse_text_integer_magnitude int32_min int32_max input)
      as [integer | |] eqn:Hparse; try discriminate.
    destruct (int32_checked integer) as [value |] eqn:Hchecked;
      try discriminate.
    intro Hvalue; inversion Hvalue; subst value.
    exists integer; now split.
  - intros [integer [Hparse Hchecked]].
    unfold parse_text_int32; now rewrite Hparse, Hchecked.
Qed.

Lemma parse_text_int64_value_iff : forall input result,
  parse_text_int64 input = TextIntegerValue result <->
  exists integer,
    parse_text_integer_magnitude int64_min int64_max input =
      TextIntegerValue integer /\
    int64_checked integer = Some result.
Proof.
  intros input result; split.
  - unfold parse_text_int64.
    destruct (parse_text_integer_magnitude int64_min int64_max input)
      as [integer | |] eqn:Hparse; try discriminate.
    destruct (int64_checked integer) as [value |] eqn:Hchecked;
      try discriminate.
    intro Hvalue; inversion Hvalue; subst value.
    exists integer; now split.
  - intros [integer [Hparse Hchecked]].
    unfold parse_text_int64; now rewrite Hparse, Hchecked.
Qed.
