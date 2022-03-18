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

Require Import List NArith.
Require Import Sql Values GenericInstance SqlSyntax Plugins.


(* Unit tests *)
(* Unit tests *)
(* schema *)

Definition db_unit0 := init_db.

Parse_sql "create table r(a integer);" create_table_unitr.
(*
Print create_table_unitr.
create_table_unitr = 
fun db : db_state => create_table db (Rel "r") (Attr_N 0 "r.a" :: nil)
     : db_state -> db_state
*)

Parse_sql "create table s(a integer);" create_table_units.
(*
Print create_table_units.
create_table_units = 
fun db : db_state => create_table db (Rel "s") (Attr_N 0 "s.a" :: nil)
     : db_state -> db_state
*)

Definition db_null := create_table_units (create_table_unitr db_unit0).

(* insert into r values (1);
insert into r values (NULL);
insert into s values (1); *)

Parse_sql "insert into r values (1), (NULL);" insert_table_r.
Parse_sql "insert into s values (1);" insert_table_s.

Definition db_unit := insert_table_s (insert_table_r db_null).

Definition eval_qu qu := eval_sql_query_in_state db_unit qu.

Parse_sql "select * from r;" q_r.

Eval vm_compute in (eval_qu q_r). 

Parse_sql "select r.a from r where r.a not in (select s.a from s);"  qnull1.
(*
Print qnull1.
qnull1 = 
_Sql_Select
  (_Select_List (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "r.a"))) (Attr_N 0 "r.a") :: nil))
  (_From_Item (_Sql_Table (Rel "r")) _Att_Ren_Star :: nil)
  (_Sql_Not
     (_Sql_In (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "r.a"))) (Attr_N 0 "s.a") :: nil)
        (_Sql_Select
           (_Select_List
              (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "s.a"))) (Attr_N 0 "s.a") :: nil))
           (_From_Item (_Sql_Table (Rel "s")) _Att_Ren_Star :: nil) _Sql_True _Group_Fine
           _Sql_True))) _Group_Fine _Sql_True
     : sql_query TNull relname predicate symbol aggregate 
*)

(*
postgres=# select r.a from r where r.a not in (select s.a from s );
 a 
---
(0 rows)
*)
Eval vm_compute in (eval_qu qnull1). 
(*     = nil
     : list (list (FlatData.Tuple.attribute TNull * FlatData.Tuple.value TNull))
*)

Parse_sql "select r.a from r where not exists (select * from s where s.a = r.a);" qnull2.
(*
Print qnull2.
qnull2 = 
_Sql_Select
  (_Select_List (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "r.a"))) (Attr_N 0 "r.a") :: nil))
  (_From_Item (_Sql_Table (Rel "r")) _Att_Ren_Star :: nil)
  (_Sql_Not
     (_Sql_Exists
        (_Sql_Select _Select_Star (_From_Item (_Sql_Table (Rel "s")) _Att_Ren_Star :: nil)
           (_Sql_Pred (Predicate "=")
              (_A_Expr (__Sql_Dot (Attr_N 0 "s.a"))
               :: _A_Expr (__Sql_Dot (Attr_N 0 "r.a")) :: nil)) _Group_Fine _Sql_True)))
  _Group_Fine _Sql_True
     : sql_query TNull relname predicate symbol aggregate
*)

(*postgres=# select r.a from r where not exists (select * from s where s.a = r.a);
 a 
---
  
(1 row)
*)

Eval vm_compute in (eval_qu qnull2). 
(*
    = ((Attr_N 0 "r.a", Value_N None) :: nil) :: nil
     : list (list (FlatData.Tuple.attribute TNull * FlatData.Tuple.value TNull))
*)

Parse_sql "select r.a from r except select s.a from s;" qnull3.
(*
Print qnull3.
qnull3 = 
_Sql_Set _Diff
  (_Sql_Select
     (_Select_List (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "r.a"))) (Attr_N 0 "r.a") :: nil))
     (_From_Item (_Sql_Table (Rel "r")) _Att_Ren_Star :: nil) _Sql_True _Group_Fine _Sql_True)
  (_Sql_Select
     (_Select_List (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "s.a"))) (Attr_N 0 "r.a") :: nil))
     (_From_Item
        (_Sql_Select
           (_Select_List
              (_Select_As (_A_Expr (__Sql_Dot (Attr_N 0 "s.a"))) (Attr_N 0 "s.a") :: nil))
           (_From_Item (_Sql_Table (Rel "s")) _Att_Ren_Star :: nil) _Sql_True _Group_Fine
           _Sql_True) _Att_Ren_Star :: nil) _Sql_True _Group_Fine _Sql_True)
     : sql_query TNull relname predicate symbol aggregate
*)

(*
postgres=# select r.a from r except select s.a from s;
 a 
---
  
(1 row)
*)

Eval vm_compute in (eval_qu qnull3). 
(*     = ((Attr_N 0 "r.a", Value_N None) :: nil) :: nil
     : list (list (FlatData.Tuple.attribute TNull * FlatData.Tuple.value TNull))
*)

                                      


