(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                         SQL ordering over tuple lists                           *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import OrderedSet FlatData.

Section Sec.

Hypothesis T : Tuple.Rcd.

Import Tuple.

Local Definition value := value T.
Local Definition attribute := attribute T.
Local Definition tuple := tuple T.

Inductive sort_direction : Type :=
  | Sort_Asc
  | Sort_Desc.

Inductive null_direction : Type :=
  | Nulls_First
  | Nulls_Last.

Record sort_key : Type :=
  mk_sort_key
    {
      sort_key_attribute : attribute;
      sort_key_direction : sort_direction;
      sort_key_null_direction : null_direction;
      (** SQL order is a semantic operation, not the structural [OVal] order
          used to implement finite collections.  Store the comparison chosen
          by the concrete SQL value model together with the symmetry law used
          by the generic list-order facts. *)
      sort_key_value_compare : value -> value -> comparison;
      sort_key_value_compare_opposite :
        forall left right,
          sort_key_value_compare left right =
          CompOpp (sort_key_value_compare right left)
    }.

Definition reverse_comparison (c : comparison) :=
  match c with
  | Lt => Gt
  | Eq => Eq
  | Gt => Lt
  end.

Definition compare_order_value
    (value_is_null : value -> bool)
    (value_compare : value -> value -> comparison)
    (direction : sort_direction)
    (nulls : null_direction)
    (left right : value) :=
  match value_is_null left, value_is_null right with
  | true, true => Eq
  | true, false =>
      match nulls with
      | Nulls_First => Lt
      | Nulls_Last => Gt
      end
  | false, true =>
      match nulls with
      | Nulls_First => Gt
      | Nulls_Last => Lt
      end
  | false, false =>
    match direction with
    | Sort_Asc => value_compare left right
    | Sort_Desc => reverse_comparison (value_compare left right)
    end
  end.

Definition compare_order_key
    (value_is_null : value -> bool)
    (key : sort_key)
    (left right : tuple) :=
  compare_order_value
    value_is_null
    (sort_key_value_compare key)
    (sort_key_direction key)
    (sort_key_null_direction key)
    (dot T left (sort_key_attribute key))
    (dot T right (sort_key_attribute key)).

Fixpoint compare_order_keys
    (value_is_null : value -> bool)
    (keys : list sort_key)
    (left right : tuple) :=
  match keys with
  | nil => Eq
  | key :: rest =>
      match compare_order_key value_is_null key left right with
      | Eq => compare_order_keys value_is_null rest left right
      | c => c
      end
  end.

Definition ordered_pair
    (value_is_null : value -> bool)
    (keys : list sort_key)
    (left right : tuple) : Prop :=
  match compare_order_keys value_is_null keys left right with
  | Gt => False
  | Eq | Lt => True
  end.

Fixpoint ordered_rows
    (value_is_null : value -> bool)
    (keys : list sort_key)
    (rows : list tuple) : Prop :=
  match rows with
  | nil | _ :: nil => True
  | row1 :: ((row2 :: _) as tail) =>
      ordered_pair value_is_null keys row1 row2 /\
      ordered_rows value_is_null keys tail
  end.

End Sec.
