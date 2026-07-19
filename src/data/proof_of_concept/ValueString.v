(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                 PostgreSQL character typmods and coercions                     *)
(**                                                                                 *)
(************************************************************************************)

Require Import Arith NArith ZArith String Ascii List Bool.
Require Import OrderedSet.

(**
  [StringText] and unbounded [StringVarchar] share the same value-level
  operations, but remain distinct typmods because result types are observable.
  [StringVarcharN n] constrains the number of characters without padding.
  [StringChar n] is PostgreSQL CHARACTER(n): values have a fixed declared width.
  [StringBpchar] is PostgreSQL's typmodless [bpchar] base type, which arises
  during operator and common-type resolution.  It has blank-padded comparison
  semantics but no width at which values may be truncated or padded.

  Rocq [string] stores bytes.  The character-width operations below validate
  UTF-8 and count Unicode code points so PostgreSQL typmods do not split a
  multibyte character.  Collations remain a separate semantic layer.
 *)
Inductive string_typmod : Set :=
  | StringText
  | StringVarchar
  | StringVarcharN (limit : nat)
  | StringChar (width : nat)
  | StringBpchar.

Register string_typmod as datacert.string_typmod.type.
Register StringText as datacert.string_typmod.StringText.
Register StringVarchar as datacert.string_typmod.StringVarchar.
Register StringVarcharN as datacert.string_typmod.StringVarcharN.
Register StringChar as datacert.string_typmod.StringChar.
Register StringBpchar as datacert.string_typmod.StringBpchar.

Definition string_typmod_key (typmod : string_typmod) : N * N :=
  match typmod with
  | StringText => (0%N, 0%N)
  | StringVarchar => (1%N, 0%N)
  | StringVarcharN limit => (2%N, N.of_nat limit)
  | StringChar width => (3%N, N.of_nat width)
  | StringBpchar => (4%N, 0%N)
  end.

Lemma string_typmod_key_injective :
  forall left right,
    string_typmod_key left = string_typmod_key right -> left = right.
Proof.
intros [| | left | left |] [| | right | right |]; simpl; intro Heq;
  try discriminate; try reflexivity.
- injection Heq as Hlength.
  apply Nat2N.inj in Hlength; subst; reflexivity.
- injection Heq as Hlength.
  apply Nat2N.inj in Hlength; subst; reflexivity.
Qed.

Definition OStringTypmod : Oset.Rcd string_typmod.
Proof.
split with
  (fun left right =>
    Oset.compare (mk_opairs ON ON)
      (string_typmod_key left) (string_typmod_key right)).
- intros left right.
  generalize
    (Oset.eq_bool_ok (mk_opairs ON ON)
      (string_typmod_key left) (string_typmod_key right)).
  destruct (Oset.compare (mk_opairs ON ON)
    (string_typmod_key left) (string_typmod_key right)); intro Hcompare.
  + now apply string_typmod_key_injective.
  + intro Heq; subst; apply Hcompare; reflexivity.
  + intro Heq; subst; apply Hcompare; reflexivity.
- intros left middle right Hleft Hright.
  exact (Oset.compare_lt_trans (mk_opairs ON ON)
    (string_typmod_key left) (string_typmod_key middle)
    (string_typmod_key right) Hleft Hright).
- intros left right.
  exact (Oset.compare_lt_gt (mk_opairs ON ON)
    (string_typmod_key left) (string_typmod_key right)).
Defined.

Definition option_string_compare (first second : option string) : comparison :=
  match first, second with
  | Some first_value, Some second_value =>
      string_compare first_value second_value
  | Some _, None => Gt
  | None, Some _ => Lt
  | None, None => Eq
  end.

Definition OOptionString : Oset.Rcd (option string).
Proof.
split with option_string_compare.
- intros [first |] [second |]; simpl.
  + case_eq (string_compare first second); intro Hcompare.
    * apply f_equal.
      apply (proj1 (Oset.compare_eq_iff Ostring first second)); exact Hcompare.
    * intro Heq; injection Heq as Heq; subst.
      change (Oset.compare Ostring second second = Lt) in Hcompare.
      rewrite Oset.compare_eq_refl in Hcompare; discriminate.
    * intro Heq; injection Heq as Heq; subst.
      change (Oset.compare Ostring second second = Gt) in Hcompare.
      rewrite Oset.compare_eq_refl in Hcompare; discriminate.
  + discriminate.
  + discriminate.
  + reflexivity.
- intros [first |] [middle |] [last |]; simpl; try discriminate; trivial.
  apply (Oset.compare_lt_trans Ostring).
- intros [first |] [second |]; simpl; try reflexivity.
  apply (Oset.compare_lt_gt Ostring).
Defined.

(** A string value carries its typmod even when its SQL payload is NULL. *)
Definition string_value : Set := (string_typmod * option string)%type.

Definition StringValue
    (typmod : string_typmod) (payload : option string) : string_value :=
  (typmod, payload).

Definition OStringValue : Oset.Rcd string_value :=
  mk_opairs OStringTypmod OOptionString.

Definition ascii_is_space (character : ascii) : bool :=
  Ascii.eqb character (Ascii.ascii_of_nat 32).

Fixpoint string_to_ascii_list (value : string) : list ascii :=
  match value with
  | EmptyString => nil
  | String character rest => character :: string_to_ascii_list rest
  end.

Fixpoint ascii_list_to_string (value : list ascii) : string :=
  match value with
  | nil => EmptyString
  | character :: rest => String character (ascii_list_to_string rest)
  end.

Fixpoint drop_leading_spaces (value : list ascii) : list ascii :=
  match value with
  | nil => nil
  | character :: rest =>
      if ascii_is_space character then drop_leading_spaces rest else value
  end.

Definition string_rtrim_spaces (value : string) : string :=
  ascii_list_to_string
    (rev (drop_leading_spaces (rev (string_to_ascii_list value)))).

Definition byte_in_range (lower upper value : nat) : bool :=
  andb (Nat.leb lower value) (Nat.leb value upper).

Definition utf8_continuation_byte (character : ascii) : bool :=
  byte_in_range 128 191 (nat_of_ascii character).

Definition utf8_second_byte_valid
    (first second : ascii) : bool :=
  let first := nat_of_ascii first in
  let second := nat_of_ascii second in
  if Nat.eqb first 224 then byte_in_range 160 191 second
  else if Nat.eqb first 237 then byte_in_range 128 159 second
  else if Nat.eqb first 240 then byte_in_range 144 191 second
  else if Nat.eqb first 244 then byte_in_range 128 143 second
  else byte_in_range 128 191 second.

(** Split one well-formed UTF-8 code point from a Rocq byte string. *)
Definition utf8_split_first (value : string) : option (string * string) :=
  match value with
  | EmptyString => None
  | String first rest =>
      let first_byte := nat_of_ascii first in
      if Nat.leb first_byte 127
      then Some (String first EmptyString, rest)
      else if byte_in_range 194 223 first_byte
      then
        match rest with
        | String second tail =>
            if utf8_continuation_byte second
            then Some (String first (String second EmptyString), tail)
            else None
        | EmptyString => None
        end
      else if byte_in_range 224 239 first_byte
      then
        match rest with
        | String second (String third tail) =>
            if andb (utf8_second_byte_valid first second)
                    (utf8_continuation_byte third)
            then Some
              (String first (String second (String third EmptyString)), tail)
            else None
        | _ => None
        end
      else if byte_in_range 240 244 first_byte
      then
        match rest with
        | String second (String third (String fourth tail)) =>
            if andb (utf8_second_byte_valid first second)
                 (andb (utf8_continuation_byte third)
                       (utf8_continuation_byte fourth))
            then Some
              (String first
                (String second (String third (String fourth EmptyString))), tail)
            else None
        | _ => None
        end
      else None
  end.

Fixpoint utf8_character_length_fuel
    (fuel : nat) (value : string) : option nat :=
  match value with
  | EmptyString => Some O
  | _ =>
      match fuel with
      | O => None
      | S fuel =>
          match utf8_split_first value with
          | Some (_, tail) =>
              match utf8_character_length_fuel fuel tail with
              | Some length => Some (S length)
              | None => None
              end
          | None => None
          end
      end
  end.

Definition utf8_character_length (value : string) : option nat :=
  utf8_character_length_fuel (String.length value) value.

Definition string_is_valid_utf8 (value : string) : bool :=
  match utf8_character_length value with Some _ => true | None => false end.

Fixpoint string_take_fuel
    (fuel count : nat) (value : string) : option string :=
  match count with
  | O => Some EmptyString
  | S count =>
      match value with
      | EmptyString => Some EmptyString
      | _ =>
          match fuel with
          | O => None
          | S fuel =>
              match utf8_split_first value with
              | Some (prefix, tail) =>
                  match string_take_fuel fuel count tail with
                  | Some suffix => Some (String.append prefix suffix)
                  | None => None
                  end
              | None => None
              end
          end
      end
  end.

Definition string_take (count : nat) (value : string) : string :=
  match string_take_fuel (String.length value) count value with
  | Some result => result
  | None => value
  end.

Fixpoint string_drop_fuel
    (fuel count : nat) (value : string) : option string :=
  match count with
  | O => Some value
  | S count =>
      match value with
      | EmptyString => Some EmptyString
      | _ =>
          match fuel with
          | O => None
          | S fuel =>
              match utf8_split_first value with
              | Some (_, tail) => string_drop_fuel fuel count tail
              | None => None
              end
          end
      end
  end.

Definition string_drop (count : nat) (value : string) : string :=
  match string_drop_fuel (String.length value) count value with
  | Some result => result
  | None => value
  end.

Fixpoint string_all_spaces (value : string) : bool :=
  match value with
  | EmptyString => true
  | String character rest =>
      andb (ascii_is_space character) (string_all_spaces rest)
  end.

Fixpoint string_spaces (count : nat) : string :=
  match count with
  | O => EmptyString
  | S count => String (Ascii.ascii_of_nat 32) (string_spaces count)
  end.

Definition string_pad_right (width : nat) (value : string) : string :=
  match utf8_character_length value with
  | Some length => String.append value (string_spaces (width - length))
  | None => value
  end.

(**
  Logical CHARACTER payloads are canonicalized by truncating to the declared
  width and dropping trailing spaces.  Physical blank padding is reconstructed
  by [string_physical_value] for operations, such as pattern matching, where the
  padding is observable.
 *)
Definition string_canonical_value
    (typmod : string_typmod) (value : string) : string :=
  match typmod with
  | StringChar width => string_rtrim_spaces (string_take width value)
  | StringBpchar => string_rtrim_spaces value
  | StringText | StringVarchar | StringVarcharN _ => value
  end.

Definition string_physical_value
    (typmod : string_typmod) (value : string) : string :=
  match typmod with
  | StringChar width =>
      string_pad_right width (string_canonical_value typmod value)
  | StringText | StringVarchar | StringVarcharN _ | StringBpchar => value
  end.

(**
  Exact PostgreSQL [LIKE] semantics for the frontend's terminal-wildcard
  subset.  The frontend admits only patterns whose sole metacharacter is one
  final unescaped [%], removes that [%], and supplies the remaining literal
  prefix here.  Consequently matching is precisely a prefix test.

  [CHARACTER(n)] is intentionally tested through its physical, blank-padded
  value.  PostgreSQL pattern matching observes those padding characters even
  though ordinary bpchar equality ignores them.  The prefix is already
  decoded from the pattern by the frontend, so its carrier typmod is not part
  of this operation.
 *)
Definition string_like_prefix
    (input_typmod : string_typmod) (input prefix : string) : bool :=
  String.prefix prefix (string_physical_value input_typmod input).

(** Match the exact PostgreSQL [LIKE] fragment whose only metacharacter is an
    unescaped percent sign.  The Rust frontend admits this operator only for a
    decoded source literal pattern with no [_] and no escape syntax.

    PostgreSQL defines [%] over characters, not bytes.  Both the literal and
    wildcard branches therefore advance with [utf8_split_first].  The fuel is
    measured in bytes, which is a conservative upper bound on the number of
    UTF-8 code points consumed along any branch.  As with [string_like_prefix],
    fixed-width CHARACTER input is matched in its blank-padded physical form.
    The trusted frontend rejects typmodless bpchar here: its logical carrier
    has discarded trailing spaces but carries no width from which to restore
    PostgreSQL's physical payload.
 *)
Definition ascii_is_percent (character : ascii) : bool :=
  Ascii.eqb character (Ascii.ascii_of_nat 37).

Definition string_codepoint_eqb (left right : string) : bool :=
  match string_compare left right with Eq => true | Lt | Gt => false end.

Fixpoint string_like_percent_fuel
    (fuel : nat) (input pattern : string) : bool :=
  match pattern with
  | EmptyString =>
      match input with EmptyString => true | String _ _ => false end
  | String first _ =>
      match fuel with
      | O => false
      | S fuel =>
          if ascii_is_percent first
          then
            orb
              (match utf8_split_first pattern with
               | Some (_, pattern_tail) =>
                   string_like_percent_fuel fuel input pattern_tail
               | None => false
               end)
              (match utf8_split_first input with
               | Some (_, input_tail) =>
                   string_like_percent_fuel fuel input_tail pattern
               | None => false
               end)
          else
            match utf8_split_first input, utf8_split_first pattern with
            | Some (input_head, input_tail),
              Some (pattern_head, pattern_tail) =>
                andb (string_codepoint_eqb input_head pattern_head)
                     (string_like_percent_fuel fuel input_tail pattern_tail)
            | _, _ => false
            end
      end
  end.

Definition string_like_percent
    (input_typmod : string_typmod) (input pattern : string) : bool :=
  let physical_input := string_physical_value input_typmod input in
  string_like_percent_fuel
    (S (String.length physical_input + String.length pattern))
    physical_input pattern.

Lemma string_like_prefix_empty :
  forall input_typmod input,
    string_like_prefix input_typmod input EmptyString = true.
Proof.
intros input_typmod input.
unfold string_like_prefix.
destruct (string_physical_value input_typmod input); reflexivity.
Qed.

Lemma string_like_prefix_text :
  forall input prefix,
    string_like_prefix StringText input prefix = String.prefix prefix input.
Proof. reflexivity. Qed.

Lemma string_like_prefix_char_physical :
  forall width input prefix,
    string_like_prefix (StringChar width) input prefix =
    String.prefix prefix
      (string_pad_right width
        (string_canonical_value (StringChar width) input)).
Proof. reflexivity. Qed.

Lemma string_like_percent_empty_pattern :
  forall input_typmod input,
    string_like_percent input_typmod input EmptyString =
    match string_physical_value input_typmod input with
    | EmptyString => true
    | String _ _ => false
    end.
Proof.
intros input_typmod input.
unfold string_like_percent.
destruct (string_physical_value input_typmod input); reflexivity.
Qed.

Definition string_fits_typmod
    (typmod : string_typmod) (value : string) : bool :=
  match utf8_character_length value with
  | None => false
  | Some length =>
      match typmod with
      | StringText | StringVarchar | StringBpchar => true
      | StringVarcharN limit | StringChar limit => Nat.leb length limit
      end
  end.

(**
  PostgreSQL assignment rejects over-length values unless every excess
  character is a space.  CHARACTER values are stored canonically; padding can
  always be reconstructed from the width.
 *)
Definition string_assignment_coerce
    (typmod : string_typmod) (value : string) : option string :=
  match typmod with
  | StringText | StringVarchar =>
      if string_is_valid_utf8 value then Some value else None
  | StringBpchar =>
      if string_is_valid_utf8 value
      then Some (string_canonical_value typmod value)
      else None
  | StringVarcharN limit =>
      match utf8_character_length value with
      | None => None
      | Some length =>
          if Nat.leb length limit
          then Some value
          else if string_all_spaces (string_drop limit value)
               then Some (string_take limit value)
               else None
      end
  | StringChar width =>
      match utf8_character_length value with
      | None => None
      | Some length =>
          if Nat.leb length width
          then Some (string_canonical_value typmod value)
          else if string_all_spaces (string_drop width value)
               then Some (string_canonical_value typmod value)
               else None
      end
  end.

(** Explicit casts truncate over-length values instead of raising an error. *)
Definition string_explicit_cast
    (typmod : string_typmod) (value : string) : string :=
  match typmod with
  | StringText | StringVarchar => value
  | StringVarcharN limit => string_take limit value
  | StringChar _ | StringBpchar => string_canonical_value typmod value
  end.

(**
  Character casts first expose the source type's SQL value and then apply the
  target typmod. Conversion from either CHARACTER form removes blank padding.
  Typmodless bpchar is also canonicalized because every currently modeled SQL
  observation (comparison, grouping, and set equality) ignores those spaces;
  byte-level observations such as octet_length remain outside this model.
 *)
Definition string_cast_source_value
    (source : string_typmod) (value : string) : string :=
  match source with
  | StringChar _ | StringBpchar => string_rtrim_spaces value
  | _ => value
  end.

(** Exact total subset of PostgreSQL's three-argument text [substring].  The
    frontend supplies a one-based literal start of at least one and a literal
    nonnegative count, so this helper receives the already-normalized number
    of characters to drop.  Conversion from CHARACTER to text removes trailing
    padding before the code-point slice, as PostgreSQL does. *)
Definition string_substring_nonnegative
    (input_typmod : string_typmod) (input : string)
    (start_offset count : nat) : string :=
  string_take count
    (string_drop start_offset (string_cast_source_value input_typmod input)).

Lemma string_substring_nonnegative_zero_count :
  forall input_typmod input start_offset,
    string_substring_nonnegative input_typmod input start_offset O = EmptyString.
Proof.
intros input_typmod input start_offset.
unfold string_substring_nonnegative, string_take.
destruct (string_drop start_offset
  (string_cast_source_value input_typmod input)); reflexivity.
Qed.

Definition string_cast_value
    (source target : string_typmod) (value : string) : string :=
  string_explicit_cast target (string_cast_source_value source value).

Definition string_semantic_value
    (typmod : string_typmod) (value : string) : string :=
  match typmod with
  | StringChar _ | StringBpchar => string_rtrim_spaces value
  | StringText | StringVarchar | StringVarcharN _ => value
  end.

Definition string_typmod_is_char (typmod : string_typmod) : bool :=
  match typmod with StringChar _ | StringBpchar => true | _ => false end.

Definition string_typmod_is_text (typmod : string_typmod) : bool :=
  match typmod with StringText => true | _ => false end.

(**
  PostgreSQL resolves mixed CHARACTER/VARCHAR comparisons through the bpchar
  comparison domain, so trailing spaces on both operands are insignificant.
  Mixed CHARACTER/TEXT comparisons instead convert CHARACTER to TEXT, which
  removes the CHARACTER padding while preserving trailing spaces in the TEXT
  operand.  Keeping this pairwise rule here avoids treating every string type
  as if it shared one equality operator.
 *)
Definition string_comparison_values
    (left_typmod : string_typmod) (left : string)
    (right_typmod : string_typmod) (right : string) : string * string :=
  if andb
       (orb (string_typmod_is_char left_typmod)
            (string_typmod_is_char right_typmod))
       (negb (orb (string_typmod_is_text left_typmod)
                  (string_typmod_is_text right_typmod)))
  then (string_rtrim_spaces left, string_rtrim_spaces right)
  else (string_semantic_value left_typmod left,
        string_semantic_value right_typmod right).

Definition sql_string_compare
    (left_typmod : string_typmod) (left : string)
    (right_typmod : string_typmod) (right : string) : comparison :=
  let '(left_value, right_value) :=
    string_comparison_values left_typmod left right_typmod right in
  string_compare left_value right_value.

Definition sql_string_eqb
    (left_typmod : string_typmod) (left : string)
    (right_typmod : string_typmod) (right : string) : bool :=
  match sql_string_compare left_typmod left right_typmod right with
  | Eq => true
  | Lt | Gt => false
  end.

Open Scope Z_scope.

Definition string_typmod_tag (typmod : string_typmod) : Z :=
  match typmod with
  | StringText => 0
  | StringVarchar => 1
  | StringVarcharN _ => 2
  | StringChar _ => 3
  | StringBpchar => 4
  end.

Definition string_typmod_length (typmod : string_typmod) : Z :=
  match typmod with
  | StringVarcharN limit | StringChar limit => Z.of_nat limit
  | StringText | StringVarchar | StringBpchar => 0
  end.

Definition string_typmod_descriptor (typmod : string_typmod) : Z * Z :=
  (string_typmod_tag typmod, string_typmod_length typmod).

Lemma string_typmod_descriptor_injective :
  forall left right,
    string_typmod_descriptor left = string_typmod_descriptor right ->
    left = right.
Proof.
intros [| | left | left |] [| | right | right |];
  cbn [string_typmod_descriptor string_typmod_tag string_typmod_length];
  intro Heq; try discriminate; try reflexivity.
- injection Heq as Hlength.
  apply Nat2Z.inj in Hlength; subst; reflexivity.
- injection Heq as Hlength.
  apply Nat2Z.inj in Hlength; subst; reflexivity.
Qed.

Definition string_typmod_from_codes (tag length : Z) : option string_typmod :=
  match tag with
  | 0 => Some StringText
  | 1 => Some StringVarchar
  | 2 => if 0 <? length
         then Some (StringVarcharN (Z.to_nat length)) else None
  | 3 => if 0 <? length
         then Some (StringChar (Z.to_nat length)) else None
  | 4 => if length =? 0 then Some StringBpchar else None
  | _ => None
  end.
