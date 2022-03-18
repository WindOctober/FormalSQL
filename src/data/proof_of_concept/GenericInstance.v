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

Require Import NArith String List. 
Require Import ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection 
        FlatData Values TuplesImpl.

(** * Definition of relation's names, and finite sets of relation's names *)

Inductive relname : Set := Rel : string -> relname.

Register relname as datacert.relname.type.
Register Rel as datacert.relname.Rel.

Definition ORN : Oset.Rcd relname.
split with (fun r1 r2 => match r1, r2 with Rel s1, Rel s2 => Oset.compare Ostring s1 s2 end).
- intros [s1] [s2].
  generalize (Oset.eq_bool_ok Ostring s1 s2).
  case (Oset.compare Ostring s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply Oset.compare_lt_trans.
- intros [s1] [s2]; apply Oset.compare_lt_gt.
Defined.


(* (** ** Definition of variable names *) *)
(* Inductive varname : Set := VarN : N -> varname. *)

(* Definition VarN_of_N := VarN. *)
(* Definition N_of_VarN : varname -> N :=  *)
(*  fun a => match a with VarN n => n end. *)

(* Definition OVN : Oset.Rcd varname. *)
(* apply Oemb with N_of_VarN. *)
(* intros [a1] [a2] H; simpl in H; apply f_equal; assumption. *)
(* Defined. *)

(** * Definition of attributes, and finite sets of attributes *)

(** There are several constructors for attributes, one for each type. This allows to have an infinite number of attributes, usefull for renaming for instance, but also to a generic function [type_of_attribute]. *)
Inductive attribute : Set :=
  | Attr_string : string -> attribute
  | Attr_Z : string -> attribute
  | Attr_bool : string -> attribute.

Register attribute as datacert.attribute.type.
Register Attr_string as datacert.attribute.Attr_string.
Register Attr_Z as datacert.attribute.Attr_Z.
Register Attr_bool as datacert.attribute.Attr_bool.

Definition type_of_attribute (a : attribute) :=
  match a with
    | Attr_string _ => type_string
    | Attr_Z _ => type_Z
    | Attr_bool _  => type_bool
  end.

Open Scope N_scope.

Definition N_of_attribute a := 
  match a with   
    | Attr_string _ => 0
    | Attr_Z _ => 1
    | Attr_bool _ => 2
  end.

Definition N2_of_attribute a :=
  match a with
    | Attr_string s
    | Attr_Z s
    | Attr_bool s => (N_of_attribute a, s)
  end.

Definition attribute_compare a1 a2 :=
  compareAB N.compare string_compare (N2_of_attribute a1) (N2_of_attribute a2).

Definition OAN : Oset.Rcd attribute.
Proof.
split with attribute_compare.
- intros a1 a2; unfold attribute_compare.
  assert (match compareAB N.compare string_compare
                           (N2_of_attribute a1) (N2_of_attribute a2) with
             | Eq => (N2_of_attribute a1) = (N2_of_attribute a2)
             | Lt => (N2_of_attribute a1) <> (N2_of_attribute a2)
             | Gt => (N2_of_attribute a1) <> (N2_of_attribute a2)
           end).
  {
    destruct (N2_of_attribute a1) as [n1 s1];
    destruct (N2_of_attribute a2) as [n2 s2].
    compareAB_eq_bool_ok_tac.
    - apply (Oset.eq_bool_ok ON).
    - apply (Oset.eq_bool_ok Ostring).
  }
  case_eq (N2_of_attribute a1); intros n1 s1 H1;
  case_eq (N2_of_attribute a2); intros n2 s2 H2;
  rewrite H1, H2 in H.
  destruct (compareAB 
              N.compare string_compare
              (n1, s1) (n2, s2)).
  + injection H; clear H; do 2 intro.
    subst s2 n2; rewrite <- H2 in H1.
    destruct a1; destruct a2; (try discriminate H1) || (injection H1; intros; subst; trivial).
  + intro Ha; apply H; rewrite <- Ha in H2; rewrite H1 in H2.
    apply H2.
  + intro Ha; apply H; rewrite <- Ha in H2; rewrite H1 in H2.
    apply H2.
- intros a1 a2 a3; unfold attribute_compare.
  compareAB_tac.
  + apply (Oset.compare_eq_trans ON).
  + apply (Oset.compare_eq_lt_trans ON).
  + apply (Oset.compare_lt_eq_trans ON).
  + apply (Oset.compare_lt_trans ON).
  + apply (Oset.compare_lt_trans Ostring).
- intros a1 a2; unfold attribute_compare.
  compareAB_tac.
  + apply (Oset.compare_lt_gt ON).
  + apply (Oset.compare_lt_gt Ostring).
Defined.

Definition FAN := Fset.build OAN.


Section Sec.

Hypothesis T : Tuple.Rcd.
Import Tuple.

Definition show_tuple t :=
  List.map
    (fun a => (a, dot T t a))
    (Fset.elements _ (labels _ t)).

Definition show_bag_tuples x :=
  List.map show_tuple (Febag.elements (Fecol.CBag (CTuple T)) x).

Definition show_col_tuples x :=
  List.map show_tuple (Fecol.elements (CA := CTuple T) x).

Record db_state_ : Type :=
  mk_state
    {
      _relnames : list relname;
      _basesort : relname -> Fset.set (A T);
      _instance : relname -> Febag.bag (Fecol.CBag (CTuple T))
    }.

Definition show_state_ (db : db_state_) :=
  (_relnames db,
   List.map (fun r => (r, Fset.elements _ (_basesort db r))) (_relnames db),
   List.map (fun r => (r, show_bag_tuples (_instance db r))) (_relnames db)).

Definition init_db_ :=
  mk_state
    nil
    (fun _ => Fset.empty (A T))
    (fun _ => Febag.empty (Fecol.CBag (CTuple T))).

Definition create_table_
           (* old state *) db
           (* new table name *) t
           (* new table sort *) st
            :=
  mk_state
    (t :: _relnames db)
    (fun x =>
       match Oset.compare ORN x t with
         | Eq => Fset.mk_set (A T) st
         |_ => _basesort db x
       end)
    (_instance db).

Definition insert_tuple_into_
           (* old state *) db
           (* new tuple *) tpl
           (* table *) tbl
            :=
  mk_state
    (_relnames db)
    (_basesort db)
    (fun x =>
       match Oset.compare ORN x tbl with
       | Eq => Febag.add (Fecol.CBag (CTuple T)) tpl (_instance db tbl)
       |_ => _instance db x
       end).

Fixpoint insert_tuples_into_
           (* old state *) db
           (* new tuple list *) ltpl
           (* table *) tbl :=
  match ltpl with
    | nil => db
    | t :: l => insert_tuple_into_ (insert_tuples_into_ db l tbl) t tbl
  end.

(* Definition MyDBS db := DatabaseSchema.mk_R (A T) ORN (_basesort db).*)

End Sec.


Definition TNull : Tuple.Rcd :=
  Tuple2.T attribute type NullValues.value 
           type_of_attribute 
           NullValues.type_of_value 
           NullValues.default_value 
           OAN FAN NullValues.OVal NullValues.FVal
           predicate _ aggregate OP (OSymbol _ NullValues.OVal) OAgg Bool3.Bool3
           NullValues.interp_predicate NullValues.interp_symbol NullValues.interp_aggregate.

Register TNull as datacert.syntax.TNull.


(* Definition TSimple (* predicate symbol aggregate  *) *)
(*            (* (OP : Oset.Rcd predicate)  *) *)
(*            (* (OSymb : Oset.Rcd symbol) *) *)
(*            (* (OAgg : Oset.Rcd aggregate)  *) *)
(*            (* interp_pred interp_symb interp_agg *) : Tuple.Rcd := *)
(*   Tuple2.T attribute type SimpleValues.value  *)
(*            type_of_attribute *)
(*            SimpleValues.type_of_value *)
(*            (fun _ => SimpleValues.NULL) *)
(*            OAN FAN SimpleValues.OVal SimpleValues.FVal *)
(*            predicate symbol aggregate OP OSymb OAgg Bool3.Bool2 *)
(*            interp_pred interp_symb interp_agg. *)

