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

Set Implicit Arguments.

(** printing inS? $\in_?$ #∈<SUB>?</SUB># *)
(** printing inS $\in$ #∈# *)(** printing subS? $\subseteq_?$ #⊆<SUB>?</SUB># *)
(** printing subS $\subseteq$ #⊆# *)
(** printing unionS $\cup$ #⋃# *)
(** printing interS $\cap$ #⋂# *)
(** printing inI $\in_I$ #∈<SUB><I>I</I></SUB># *)
(** printing theta $\theta$ #θ# *)
(** printing nu1 $\nu_1$ #ν<SUB><I>1</I></SUB># *)
(** printing nu $\nu$ #ν# *)
(** printing mu $\mu$ #μ# *)
(** printing sigma $\sigma$ #σ# *)
(** printing -> #⟶# *)
(** printing <-> #⟷# *)
(** printing => #⟹# *)
(** printing (emptysetS) $\emptyset$ #Ø# *)
(** printing emptysetS $\emptyset$ #Ø# *)
(** printing {{ $\{$ #{# *)
(** printing }} $\}$ #}# *)

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet 
        FiniteSet FiniteBag FiniteCollection Join FlatData Tree Bool3 Formula 
        Partition.

(*************** SQL (Postgres) Fragment handled so far ******************
 SELECT [ ALL | DISTINCT ] * | expression [ [ AS ] output_name ] [, ...]
 [ FROM from_item [, ...] ]
 [ WHERE condition ]
 [ GROUP BY expression [, ...] ]
 [ HAVING condition [, ...] ]
 [ { UNION | INTERSECT | EXCEPT } [ ALL | DISTINCT ] select ]
   -- [ ORDER BY expression [ ASC | DESC | USING operator ] 
   -- [ NULLS { FIRST | LAST }                        ] [, ...] ]
   --     [ FETCH { FIRST | NEXT } [ count ] { ROW | ROWS } ONLY ]
   --     [ FOR { UPDATE | SHARE } [ OF table_name [, ...] ] [ NOWAIT ] [...] ]

where from_item can be one of:

    [ ONLY ] table_name [ * ] [ [ AS ] alias [ ( column_alias [, ...] ) ] ]
    ( select ) [ AS ] alias [ ( column_alias [, ...] ) ]
    with_query_name [ [ AS ] alias [ ( column_alias [, ...] ) ] ]
--     function_name ( [ argument [, ...] ] ) [ AS ] alias [ ( column_alias [, .--      ..] | column_definition [, ...] ) ]
--     function_name ( [ argument [, ...] ] ) AS ( column_definition [, ...] )
    from_item NATURAL JOIN from_item // on est conforme au modele theorique

and with_query is:

--  with_query_name [ ( column_name [, ...] ) ]
    AS ( select | insert | update | delete )

**************************************************************************)

Section Sec.

Hypothesis T : Tuple.Rcd.

Hypothesis relname : Type.
Hypothesis ORN : Oset.Rcd relname.

Notation predicate := (Tuple.predicate T).
Notation symb := (Tuple.symbol T).
Notation aggregate := (Tuple.aggregate T).
Notation OPredicate := (Tuple.OPred T).
Notation OSymb := (Tuple.OSymb T).
Notation OAggregate := (Tuple.OAgg T).

Import Tuple.

Notation value := (value T).
Notation attribute := (attribute T).
Notation tuple := (tuple T).
Arguments funterm {T}.
Arguments aggterm {T}.
Arguments Select_Star {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Arguments Group_Fine {T}.
Arguments Group_By {T}.
Arguments F_Dot {T}.
Arguments A_Expr {T}.
Arguments Sql_True {T}.
Arguments Sql_Pred {T}.
Arguments Sql_Quant {T}.
Arguments Sql_In {T}.
Arguments Sql_Exists {T}.

(** * SQL_COQ Syntax *)
Inductive att_renaming : Type :=
  | Att_As : attribute -> attribute -> att_renaming.

Register att_renaming as datacert.att_renaming.type.

Inductive att_renaming_item : Type :=
  | Att_Ren_Star
  | Att_Ren_List : list att_renaming -> att_renaming_item.

Register Att_Ren_List as datacert.att_renaming_item.Att_Ren_List.

Inductive sql_query : Type := 
  | Sql_Table : relname -> sql_query 
  | Sql_Set : set_op -> sql_query -> sql_query -> sql_query 
  | Sql_Select : 
      (** select *) select_item T ->
      (** from *) list sql_from_item ->
      (** where *) sql_formula T sql_query ->
      (** group by *) group_by T ->
      (** having *) sql_formula T sql_query -> sql_query

with sql_from_item : Type := 
  | From_Item : sql_query -> att_renaming_item -> sql_from_item.

Definition All := (All T relname).
Arguments All_relname {T} {relname}.
Arguments All_attribute {T} {relname}.
Arguments All_predicate {T} {relname}.
Arguments All_funterm {T} {relname}.
Arguments All_aggterm {T} {relname}.
Arguments tree_of_attribute {T} {relname}.
Arguments tree_of_select_item {T} {relname}.
Arguments tree_of_sql_formula {T} {dom} {relname}.

Definition tree_of_att_renaming x : tree All :=
  match x with
    | Att_As a1 a2 => Node 3 (tree_of_attribute a1 :: tree_of_attribute a2 :: nil)
  end.

Definition tree_of_att_renaming_item r : tree All :=
  match r with
    | Att_Ren_Star => Node 4 nil
    | Att_Ren_List r => Node 5 (map tree_of_att_renaming r)
  end.

Definition tree_of_group_by g : tree All :=
  match g with
    | Group_By l => Node 6 (map (fun x => Leaf (All_aggterm x)) l)
    | Group_Fine => Node 7 nil
  end.

Fixpoint tree_of_sql_query (sq : sql_query) : tree All :=
  match sq with
    | Sql_Table r => Node 8 (Leaf (All_relname r) :: nil)
    | Sql_Set o sq1 sq2 =>
      Node (match o with | Union => 9 | Inter => 10 | Diff => 11 | UnionMax => 22 end)
        (tree_of_sql_query sq1 :: tree_of_sql_query sq2 :: nil)
    | Sql_Select s f w g h =>
      let tree_of_sql_from_item :=
          fun f =>
            match f with
              | From_Item sq rho => 
                Node 12 (tree_of_sql_query sq :: tree_of_att_renaming_item rho :: nil)
            end in
      Node 13
           (tree_of_select_item s ::
           Node 6 (map tree_of_sql_from_item f) ::
           tree_of_sql_formula tree_of_sql_query w ::
           tree_of_group_by g ::
           tree_of_sql_formula tree_of_sql_query h :: nil)
  end.

Definition tree_of_sql_from_item f : tree All :=
  match f with
    | From_Item sq rho => Node 12 (tree_of_sql_query sq :: tree_of_att_renaming_item rho :: nil)
  end.

Lemma tree_of_sql_from_item_unfold :
  forall f, tree_of_sql_from_item f =
       match f with
         | From_Item sq rho => 
           Node 12 (tree_of_sql_query sq :: tree_of_att_renaming_item rho :: nil)
       end.
Proof.
intros f; case f; intros; apply refl_equal.
Qed.

Lemma tree_of_sql_query_unfold :
  forall q, tree_of_sql_query q =
  match q with
    | Sql_Table r => Node 8 (Leaf (All_relname r) :: nil)
    | Sql_Set o sq1 sq2 =>
      Node
        (match o with | Union => 9 | Inter => 10 | Diff => 11 | UnionMax => 22 end)
        (tree_of_sql_query sq1 :: tree_of_sql_query sq2 :: nil)
    | Sql_Select s f w g h =>
      Node 13
           (tree_of_select_item s ::
           Node 6 (map tree_of_sql_from_item f) ::
           tree_of_sql_formula tree_of_sql_query w ::
           tree_of_group_by g ::
           tree_of_sql_formula tree_of_sql_query h :: nil)
  end.
Proof.
  intros q; case q; intros; apply refl_equal.
Qed.

(** * Syntactic comparison of queries *)

Open Scope N_scope.

Definition N_of_All (a : All) : N :=
  match a with
    | All_relname _ => 0
    | All_attribute _ => 1
    | All_predicate _ => 2
    | All_funterm _ => 3
    | All_aggterm _ => 4
  end.

Close Scope N_scope.

Definition all_compare a1 a2 :=
   match N.compare (N_of_All a1) (N_of_All a2) with
   | Lt => Lt
   | Gt => Gt
   | Eq =>
       match a1, a2 with
       | All_relname r1, All_relname r2 => Oset.compare ORN r1 r2
       | All_attribute a1, All_attribute a2 => Oset.compare (OAtt T) a1 a2
       | All_predicate p1, All_predicate p2 => Oset.compare OPredicate p1 p2
       | All_funterm f1, All_funterm f2 => Oset.compare (OFun T) f1 f2
       | All_aggterm a1, All_aggterm a2 => 
           Oset.compare (OAggT T) a1 a2
       | _, _ => Eq
       end
   end.

Definition OAll : Oset.Rcd All.
split with all_compare; unfold all_compare.
(* 1/3 *)
- intros a1 a2.
  case a1; clear a1;
  (intro x1; case a2; clear a2; intro x2; simpl; try discriminate);
  try oset_compare_tac.
  + generalize (funterm_compare_eq_bool_ok T x1 x2).
    case (funterm_compare T x1 x2).
    * apply f_equal.
    * intros H K; apply H.
      injection K; exact (fun h => h).
    * intros H K; apply H.
      injection K; exact (fun h => h).
  + generalize (aggterm_compare_eq_bool_ok T x1 x2).
    case (aggterm_compare T x1 x2).
    * apply f_equal.
    * intros H K; apply H.
      injection K; exact (fun h => h).
    * intros H K; apply H.
      injection K; exact (fun h => h).
- intros a1 a2 a3.
  case a1; clear a1;
  (intro x1; case a2; clear a2; try discriminate; 
   (intro x2; case a3; clear a3; intro x3; simpl; 
    try (discriminate || intros; apply refl_equal)));
  try oset_compare_tac.
  + apply (Oset.compare_lt_trans (OFun T)).
  + apply (Oset.compare_lt_trans (OAggT T)).
- (* 1/1 *)
  intros a1 a2.
  case a1; clear a1; 
  (intro x1; case a2; clear a2; intro x2; simpl;
   try (discriminate || intros; apply refl_equal));
  try oset_compare_tac.
  + apply (Oset.compare_lt_gt (OFun T)).
  + apply (Oset.compare_lt_gt (OAggT T)).
Defined.

Ltac inv_tac x Hn := intros x Hn; destruct x; inversion Hn; fail.

 Ltac sql_size_tac := 
  match goal with
    | Hn : tree_size (tree_of_sql_query (Sql_Set _ ?q1 _)) <= S ?n 
      |- tree_size (tree_of_sql_query ?q1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Set _ _ ?q2)) <= S ?n 
      |- tree_size (tree_of_sql_query ?q2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n
      |- list_size (tree_size (All:=All)) (map tree_of_sql_from_item ?lsq) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      do 2 apply le_S; apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star ?lsq _ _ _)) <= S ?n,
      Hi : In ?fi ?lsq
      |- tree_size (tree_of_sql_from_item ?fi) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size; rewrite in_map_iff; eexists; split; [apply refl_equal | trivial]

    | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) ?lsq _ _ _)) <= S ?n,
           Hy : In ?y ?lsq
      |- tree_size (tree_of_sql_from_item ?y) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size; rewrite in_map_iff; 
      eexists; split; [apply refl_equal | assumption]

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n,
      Hi : In ?fi ?lsq
      |- tree_size (tree_of_sql_from_item ?fi) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply in_list_size;
      rewrite in_map_iff; exists fi; split; trivial

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ ?lsq _ _ _)) <= S ?n,
           Hf : In (From_Item ?sq ?r) ?lsq
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply (le_trans _ (tree_size (tree_of_sql_from_item (From_Item sq r))) _);
        [simpl; apply le_S; apply le_plus_l | ];
      apply in_list_size; rewrite in_map_iff; eexists; split; [ | apply Hf]; trivial

    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star _ ?f1 _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) _ ?f1 _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f1) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ _ ?f _ _)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

(*    | Hn : tree_size  (tree_of_sql_query (Sql_Select _ _ Sql_True _ ?f)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l
*)            
    | Hn : tree_size (tree_of_sql_query (Sql_Select Select_Star _ _ _ ?f2)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      do 2 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

   | Hn : tree_size (tree_of_sql_query (Sql_Select (Select_List _) _ _ _ ?f2)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f2) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S;
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      do 3 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_query (Sql_Select _ _ _ _ ?f)) <= S ?n
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_query_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); 
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_S;
      do 3 refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_from_item (From_Item ?sq _)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_from_item_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Conj _ ?f _)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      simpl; apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Conj _ _ ?f)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Not ?f)) <= S ?n 
      |- tree_size (tree_of_sql_formula _ ?f) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      simpl; apply le_plus_l

(*    | Hn : tree_size (tree_of_sql_formula (Sql_Atom ?a)) <= S ?n
      |- tree_size (tree_of_sql_atom ?a) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_plus_l *)

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Quant _ _ _ _ ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (Le.le_trans _ _ _ _ (le_plus_l _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_In _ _ ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      do 2 apply le_S;
      refine (le_trans _ _ _ _ (le_plus_l _ _));
      refine (le_trans _ _ _ _ (le_plus_r _ _));
      apply le_plus_l

    | Hn : tree_size (tree_of_sql_formula _ (Sql_Exists _ ?sq)) <= S ?n
      |- tree_size (tree_of_sql_query ?sq) <= ?n =>
      rewrite tree_of_sql_formula_unfold in Hn; simpl in Hn;
      refine (le_trans _ _ _ _ (le_S_n _ _ Hn));
      apply le_S; refine (le_trans _ _ _ _ (le_plus_l _ _));
      apply le_plus_l

    | _ => idtac
  end.


Lemma tree_of_sql_query_eq_etc :
  forall n,
  (forall q1, tree_size (tree_of_sql_query q1) <= n ->
   forall q2, tree_of_sql_query q1 = tree_of_sql_query q2 -> q1 = q2) /\

  (forall f1, tree_size (tree_of_sql_from_item f1) <= n ->
         forall f2, tree_of_sql_from_item f1 = tree_of_sql_from_item f2 -> f1 = f2) /\

  (forall f1, 
      tree_size (tree_of_sql_formula tree_of_sql_query f1) <= n ->
      forall f2, 
        tree_of_sql_formula tree_of_sql_query f1 = tree_of_sql_formula tree_of_sql_query f2 -> 
        f1 = f2).
Proof.
intro n; induction n as [ | n]; repeat split; try (inv_tac x Hn).
- intros q1 Hn q2 H. 
  destruct q1 as [r1 | o1 q11 q12 | s1 lsq1 f11 g1 f12];
    destruct q2 as [r2 | o2 q21 q22 | s2 lsq2 f21 g2 f22]; try discriminate H.
  + injection H; apply f_equal.
  + injection H; intros H2 H1 Ho; apply f_equal3.
    * destruct o1; destruct o2; try discriminate Ho; trivial.
    * apply (proj1 IHn); trivial; sql_size_tac.
    * apply (proj1 IHn); trivial; sql_size_tac.
  + rewrite 2 tree_of_sql_query_unfold in H; injection H; intros Hf2 Hg Hf1 Hlsq Hs.
    apply f_equal5.
    * destruct s1 as [ | [l1]]; destruct s2 as [ | [l2]]; trivial; try discriminate Hs.
      do 2 apply f_equal.
      injection Hs; clear Hs; intro Hs.
      clear Hn H.
      revert l2 Hs;
        induction l1 as [ | [a1 b1] l1];
        intros [ | [a2 b2] l2] Hs; try (apply refl_equal || discriminate Hs).
      simpl in Hs; injection Hs; clear Hs.
      intros Hl Hb Ha; apply f_equal2; [apply f_equal2; trivial | ].
      apply IHl1; assumption.
    * assert (IH : forall fi1, 
                      List.In fi1 lsq1 -> 
                      forall fi2, tree_of_sql_from_item fi1 = tree_of_sql_from_item fi2 -> 
                                  fi1 = fi2).
      {
        intros fi1 Hfi1 fi2 Hfi.
        apply (proj2 IHn); trivial.
        sql_size_tac.
      }
      clear Hn H; revert lsq2 Hlsq IH.
      induction lsq1 as [ | fi1 lsq1];
        intros [ | fi2 lsq2] Hlsq IH; try (apply refl_equal || discriminate Hlsq).
      simpl in Hlsq; injection Hlsq; clear Hlsq; intros Hlsq Hfi.
      apply f_equal2; [apply (IH fi1 (or_introl _ (refl_equal _)) fi2 Hfi) | ].
      apply IHlsq1; [assumption | ].
      do 2 intro; apply IH; right; assumption.
    * apply (proj2 (proj2 IHn)); [ | assumption]; sql_size_tac.
    * destruct g1 as [g1 | ]; destruct g2 as [g2 | ];
      try (apply refl_equal || discriminate Hg).
      simpl in Hg; injection Hg; clear Hg; intro Hg.
      apply f_equal.
      clear Hn H; revert g2 Hg.
      induction g1 as [ | fu1 g1]; intros [ | fu2 g2] Hg;
      try (apply refl_equal || discriminate Hg).
      simpl in Hg; injection Hg; clear Hg; intros Hg Hfu.
      apply f_equal2; [apply Hfu | ].
      apply IHg1; assumption.
    * apply (proj2 (proj2 IHn)); [ | assumption]; sql_size_tac.
- intros f1 Hn f2 H; destruct f1 as [sq1 r1]; destruct f2 as [sq2 r2].
  simpl in H; injection H; clear H.
  intros Ha Hs; apply f_equal2.
  + apply (proj1 IHn); [ | assumption]; sql_size_tac.
  + destruct r1 as [ | r1]; destruct r2 as [ | r2]; trivial; try discriminate Ha.
    simpl in Ha; injection Ha; clear Ha; intro Ha.
    apply f_equal.
    clear Hn; revert r2 Ha.
    induction r1 as [ | [a1 b1] l1];
      intros [ | [a2 b2] l2] H; trivial; try discriminate H.
    simpl in H; injection H; clear H.
    intros Hl Hb Ha; apply f_equal2; [apply f_equal2; trivial | ].
    apply IHl1; assumption.
- intros f1 Hn f2 H.
  apply (@tree_of_sql_formula_eq T sql_query relname tree_of_sql_query n).
  + apply (proj1 IHn).
  + apply Hn.
  + assumption.
Qed.

Lemma tree_of_sql_query_eq :
  forall q1 q2, tree_of_sql_query q1 = tree_of_sql_query q2 -> q1 = q2.
Proof.
intros q1 q2 H.  
apply (proj1 (tree_of_sql_query_eq_etc _) q1 (le_n _) q2 H).
Qed.

Definition OSQLQ : Oset.Rcd sql_query.
split with (fun q1 q2 => Oset.compare (OTree OAll) (tree_of_sql_query q1) (tree_of_sql_query q2)).
- intros a1 a2.
  generalize (Oset.eq_bool_ok (OTree OAll) (tree_of_sql_query a1) (tree_of_sql_query a2)).
  case (Oset.compare (OTree OAll) (tree_of_sql_query a1) (tree_of_sql_query a2)).
  + apply tree_of_sql_query_eq.
  + intros H K; apply H; subst; apply refl_equal.
  + intros H K; apply H; subst; apply refl_equal.
- do 3 intro; oset_compare_tac.
- do 2 intro; oset_compare_tac.
Defined.

Definition OFI : Oset.Rcd sql_from_item.
split with (fun q1 q2 => 
              Oset.compare (OTree OAll) (tree_of_sql_from_item q1) (tree_of_sql_from_item q2)).
- intros a1 a2.
  generalize (Oset.eq_bool_ok (OTree OAll) (tree_of_sql_from_item a1) (tree_of_sql_from_item a2)).
  case (Oset.compare (OTree OAll) (tree_of_sql_from_item a1) (tree_of_sql_from_item a2)).
  + apply (proj1 (proj2 (tree_of_sql_query_eq_etc (tree_size (tree_of_sql_from_item a1))))).
    apply le_n.
  + intros H K; apply H; subst; apply refl_equal.
  + intros H K; apply H; subst; apply refl_equal.
- do 3 intro; oset_compare_tac.
- do 2 intro; oset_compare_tac.
Defined.

(** * SQL_COQ semantics *)
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).

Hypothesis basesort : relname -> Fset.set (Tuple.A T).
Hypothesis instance : relname -> bagT.

(* Evaluation in an environment :-( *)

Notation make_groups := 
  (fun env b => @make_groups T env (Febag.elements (Fecol.CBag (CTuple T)) b)).

(** * Building a Select_List from a renaming occuring in a from part *)

Definition att_renaming_item_to_from_item x :=
  match x with
    | Att_Ren_Star => Select_Star 
    | Att_Ren_List la => 
      Select_List 
        (_Select_List (List.map 
           (fun y => 
              match y with 
                | Att_As a b => Select_As T (A_Expr (F_Dot a)) b
              end) 
           la))
  end.

(** Sort of an SQL query : a set of attributes *)
Definition select_as_as_pair (x : select T) := match x with Select_As _ e a => (e, a) end.
Definition att_as_as_pair x := match x with Att_As e a => (e, a) end.

Fixpoint sql_sort (sq : sql_query) : setA :=
  match sq with
    | Sql_Table tbl => basesort tbl
    | Sql_Set o sq1 _ => sql_sort sq1 
    | Sql_Select s f _ _ _ => 
      match s with
        | Select_Star  => Fset.Union (A T) (List.map sql_from_item_sort f)
        | Select_List (_Select_List la) => 
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map select_as_as_pair la))
      end
  end

with sql_from_item_sort x :=
  match x with
    | From_Item sq Att_Ren_Star => sql_sort sq
    | From_Item _ (Att_Ren_List la) =>
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map att_as_as_pair la))
  end.

Lemma sql_sort_unfold :
  forall sq, sql_sort sq =
  match sq with
    | Sql_Table tbl => basesort tbl
    | Sql_Set o sq1 _ => sql_sort sq1
    | Sql_Select s f _ _ _ => 
      match s with
        | Select_Star => Fset.Union (A T) (List.map sql_from_item_sort f)
        | Select_List (_Select_List la) => 
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map select_as_as_pair la))
      end
  end.
Proof.
intro sq; case sq; intros; apply refl_equal.
Qed.

Lemma sql_from_item_sort_unfold :
  forall x, sql_from_item_sort x =
  match x with
    | From_Item sq Att_Ren_Star => sql_sort sq
    | From_Item _ (Att_Ren_List la) =>
           Fset.mk_set (A T) (List.map (@snd _ _) (List.map att_as_as_pair la))
  end.
Proof.
intros x; case x; intros; apply refl_equal.
Qed.

(** * evaluation of SQL queries *)
Hypothesis unknown : Bool.b (B T).
Hypothesis contains_nulls : tuple -> bool.
Hypothesis contains_nulls_eq : forall t1 t2, t1 =t= t2 -> contains_nulls t1 = contains_nulls t2.

Notation eval_sql_formula := (eval_sql_formula (T := T) (dom := sql_query) unknown contains_nulls).

Fixpoint eval_sql_query env (sq : sql_query) {struct sq} : bagT :=
  match sq with
  | Sql_Table tbl => instance tbl
  | Sql_Set o sq1 sq2 =>
    if sql_sort sq1 =S?= sql_sort sq2 
    then Febag.interp_set_op _ o (eval_sql_query env sq1) (eval_sql_query env sq2)
    else Febag.empty _
  | Sql_Select s lsq f1 gby f2  => 
    let elsq := 
         (** evaluation of the from part *)
        List.map (eval_sql_from_item env) lsq in
    let cc :=
        (** selection of the from part by the where formula f1 (with old names) *)
        Febag.filter 
          BTupleT 
          (fun t => 
             Bool.is_true 
               _ 
               (eval_sql_formula eval_sql_query (env_t T env t) f1)) 
          (N_join_bag T elsq) in
    (** computation of the groups grouped according to gby *)
       let lg1 := make_groups env cc gby in
       (** discarding groups according the having clause f2 *)
       let lg2 := 
           List.filter 
             (fun g  => Bool.is_true _ (eval_sql_formula eval_sql_query (env_g T env gby g) f2))
             lg1 in
       (** applying the outermost projection and renaming, the select part s *)
       Febag.mk_bag BTupleT
                    (List.map (fun g => projection T (env_g T env gby g) s) lg2)
  end

(** * evaluation of the from part *)
with eval_sql_from_item env x := 
       match x with
         | From_Item sqj sj =>
           Febag.map BTupleT BTupleT 
             (fun t => 
                projection T (env_t T env t) (att_renaming_item_to_from_item sj)) 
             (eval_sql_query env sqj)
       end.


Lemma eval_sql_query_unfold :
  forall env sq, eval_sql_query env sq =
  match sq with
  | Sql_Table tbl => instance tbl
  | Sql_Set o sq1 sq2 =>
    if sql_sort sq1 =S?= sql_sort sq2 
    then Febag.interp_set_op _ o (eval_sql_query env sq1) (eval_sql_query env sq2)
    else Febag.empty _
  | Sql_Select s lsq f1 gby f2  => 
    let elsq := 
         (** evaluation of the from part *)
        List.map (eval_sql_from_item env) lsq in
    let cc :=
        (** selection of the from part by the where formula f1 (with old names) *)
        Febag.filter 
          BTupleT 
          (fun t => 
             Bool.is_true 
               _ 
               (eval_sql_formula eval_sql_query (env_t T env t) f1)) 
          (N_join_bag T elsq) in
    (** computation of the groups grouped according to gby *)
       let lg1 := make_groups env cc gby in
       (** discarding groups according the having clause f2 *)
       let lg2 := 
           List.filter 
             (fun g  => Bool.is_true _ (eval_sql_formula eval_sql_query (env_g T env gby g) f2))
             lg1 in
       (** applying the outermost projection and renaming, the select part s *)
       Febag.mk_bag BTupleT
                    (List.map (fun g => projection T (env_g T env gby g) s) lg2)
  end.
Proof.
  intros env sq; case sq; intros; apply refl_equal.
Qed.

Lemma eval_sql_from_item_unfold :
  forall env x, eval_sql_from_item env x = 
       match x with
         | From_Item sqj sj =>
           Febag.map BTupleT BTupleT 
             (fun t => 
                projection T (env_t T env t) (att_renaming_item_to_from_item sj)) 
             (eval_sql_query env sqj)
       end.
Proof.
intros env x; case x; intros; apply refl_equal.
Qed.

Lemma eval_sql_query_eq_etc :
  forall n,
    (forall q, 
       tree_size (tree_of_sql_query q) <= n -> 
       forall env1 env2, equiv_env _ env1 env2 ->
                         eval_sql_query env1 q =BE= eval_sql_query env2 q) /\
    
    (forall f, 
       tree_size (tree_of_sql_from_item f) <= n ->
       forall env1 env2, equiv_env _ env1 env2 ->
                         eval_sql_from_item env1 f =BE= eval_sql_from_item env2 f) /\
    
    (forall f, 
       tree_size (tree_of_sql_formula tree_of_sql_query f) <= n ->
       forall env1 env2, equiv_env _ env1 env2 ->
                         eval_sql_formula eval_sql_query env1 f = 
                         eval_sql_formula eval_sql_query env2 f).
Proof.
intro n; induction n as [ | n]; repeat split.
- intros q Hn; destruct q; inversion Hn.
- intros f Hn; destruct f; inversion Hn.
- intros f Hn; destruct f; inversion Hn.
- intros q Hn env1 env2 Henv; 
  destruct q as [r | o q1 q2 | s lsq f1 g f2]; rewrite Febag.nb_occ_equal; intro t.
  + apply refl_equal.
  + rewrite 2 (eval_sql_query_unfold _ (Sql_Set _ _ _)).
    assert (IH1 : eval_sql_query env1 q1 =BE= eval_sql_query env2 q1).
    {
      apply (proj1 IHn); [sql_size_tac | ]; trivial.
    }
    assert (IH2 : eval_sql_query env1 q2 =BE= eval_sql_query env2 q2).
    {
      apply (proj1 IHn); [sql_size_tac | ]; trivial.
    }
    rewrite Febag.nb_occ_equal in IH1, IH2.
    case (sql_sort q1 =S?= sql_sort q2); [ | apply refl_equal].
    destruct o; simpl.
    * rewrite 2 Febag.nb_occ_union, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_union_max, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_inter, IH1, IH2; apply refl_equal.
    * rewrite 2 Febag.nb_occ_diff, IH1, IH2; apply refl_equal.
  + rewrite 2 (eval_sql_query_unfold _ (Sql_Select _ _ _ _ _)); cbv beta iota zeta.
    rewrite 2 Febag.nb_occ_mk_bag.
    refine (trans_eq _ (Oeset.nb_occ_map_eq_3 (OLTuple T) _ _ _ _ _ _ _));
    [refine (Oeset.nb_occ_map_eq_2_alt (OLTuple T) _ _ _ _ _ _) | | ].
    * intros x1 Hx1; apply projection_eq; env_tac.
    * intros x1 x2 Hx1 Hx2 Hx; apply projection_eq; env_tac.
    * clear t; intro l.
      {
        apply Oeset.nb_occ_filter_eq.
        - clear l; intro l.
          apply make_groups_eq_bag; [assumption | ].
          apply Febag.filter_eq.
          + rewrite Febag.nb_occ_equal; intro t.
            unfold N_join_bag;rewrite 2 Febag.nb_occ_mk_bag, 2 map_map.
            apply Oeset.permut_nb_occ; apply Oeset.permut_refl_alt;
            apply N_join_list_map_eq; [apply join_tuple_eq_1 | apply join_tuple_eq_2 | ].
            intros x Hx; apply Febag.elements_spec1.
            apply (proj1 (proj2 IHn)); [sql_size_tac | trivial].
          + intros x1 x2 Hx1 Hx; apply f_equal.
            apply (proj2 (proj2 IHn)); [sql_size_tac | env_tac].
        - intros x1 x2 Hx1 Hx; apply f_equal.
          apply (proj2 (proj2 IHn)); [sql_size_tac | env_tac].
      }
- intros [sq r] Hn env1 env2 He.
  assert (IH : eval_sql_query env1 sq =BE= eval_sql_query env2 sq).
  {
    apply (proj1 IHn); [sql_size_tac | assumption].
  }
  destruct r as [ | r]; rewrite 2 (eval_sql_from_item_unfold _ (From_Item _ _)).
  + unfold Febag.map; rewrite 2 map_id; intros; trivial.
    rewrite Febag.nb_occ_equal; intro t.
    rewrite 2 Febag.nb_occ_mk_bag, <- 2 Febag.nb_occ_elements.
    rewrite Febag.nb_occ_equal in IH; apply IH.
  + rewrite Febag.nb_occ_equal; intro t.
    unfold Febag.map; rewrite 2 Febag.nb_occ_mk_bag.
    apply (Oeset.nb_occ_map_eq_2_3 (OTuple T)).
    * intros x1 x2 Hx; apply projection_eq; env_tac.
    * clear t; intro t; rewrite <- 2 Febag.nb_occ_elements.
    rewrite Febag.nb_occ_equal in IH; apply IH.
- intros f Hf env1 env2 He; apply eval_sql_formula_eq_etc with relname tree_of_sql_query n.
  + apply contains_nulls_eq.
  + apply (proj1 IHn).
  + apply Hf.
  + assumption.
Qed.

Lemma eval_sql_query_eq :
  forall q env1 env2, equiv_env T env1 env2 -> eval_sql_query env1 q =BE= eval_sql_query env2 q.
Proof.
intros q env1 env2 He.
apply (proj1 (eval_sql_query_eq_etc _) _ (le_n _) _ _ He).
Qed.

Lemma eval_sql_from_item_eq :    
  forall f env1 env2, equiv_env T env1 env2 -> 
                      eval_sql_from_item env1 f =BE= eval_sql_from_item env2 f.
Proof.
intros f env1 env2 He.
apply (proj1 (proj2 (eval_sql_query_eq_etc _)) _ (le_n _) _ _ He).
Qed.

Lemma eval_sql_formula_eq :    
  forall f env1 env2, equiv_env T env1 env2 -> 
   eval_sql_formula eval_sql_query env1 f = eval_sql_formula eval_sql_query env2 f.
Proof.
intros f env1 env2 He.
apply (proj2 (proj2 (eval_sql_query_eq_etc _)) _ (le_n _) _ _ He).
Qed.

Definition well_sorted_sql_table :=
  forall tbl t, t inBE (instance tbl) -> labels T t =S= basesort tbl.

Lemma well_sorted_sql_query_etc :
  well_sorted_sql_table -> 
  forall n, 
    (forall sq, tree_size (tree_of_sql_query sq) <= n ->
                forall t env, t inBE (eval_sql_query env sq) -> labels T t =S= sql_sort sq) /\
    (forall lf, list_size (tree_size (All:=All)) (map tree_of_sql_from_item lf) <= n ->
                forall t env, t inBE N_join_bag T (map (eval_sql_from_item env) lf) ->
                          labels T t =S= Fset.Union (A T) (map sql_from_item_sort lf)).
Proof.
intros W n; induction n as [ | n]; repeat split.
- intros sq Hn; destruct sq; inversion Hn.
- intros lf Hn; destruct lf as [ | f1 lf]; [ | destruct f1; inversion Hn].
  intros t env Ht; simpl in Ht.
  rewrite Febag.mem_nb_occ in Ht; unfold N_join_bag in Ht; simpl in Ht.
  rewrite Febag.nb_occ_add, Febag.nb_occ_empty, N.add_0_r in Ht.
  case_eq (Oeset.eq_bool (OTuple T) t (empty_tuple T)); intro Kt;
    rewrite Kt in Ht; try discriminate Ht.
  unfold Oeset.eq_bool in Kt; rewrite compare_eq_true, tuple_eq in Kt.
  rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Kt)); unfold empty_tuple.
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  simpl; apply Fset.equal_refl.
- intros sq Hn t env Ht; destruct sq as [r | o sq1 sq2 | s lsq f1 gby f2].
  + apply W; apply Ht.
  + rewrite eval_sql_query_unfold in Ht.
    rewrite sql_sort_unfold.
    case_eq (sql_sort sq1 =S?= sql_sort sq2); 
      intro Hsq; rewrite Hsq in Ht.
    * {
        destruct o; simpl in Ht.
        - rewrite Febag.mem_union, Bool.Bool.orb_true_iff in Ht.
          destruct Ht as [Ht | Ht].
          + apply (proj1 IHn) with env; [sql_size_tac | assumption].
          + rewrite (Fset.equal_eq_2 _ _ _ _ Hsq).
            apply (proj1 IHn) with env; [sql_size_tac | assumption].
        - rewrite Febag.mem_union_max, Bool.Bool.orb_true_iff in Ht.
          destruct Ht as [Ht | Ht].
          + apply (proj1 IHn) with env; [sql_size_tac | assumption].
          + rewrite (Fset.equal_eq_2 _ _ _ _ Hsq).
            apply (proj1 IHn) with env; [sql_size_tac | assumption].
        - apply (proj1 IHn) with env; [sql_size_tac | ].
          rewrite Febag.mem_inter, Bool.Bool.andb_true_iff in Ht.
          apply (proj1 Ht).
        - apply (proj1 IHn) with env; [sql_size_tac | ].
          apply (Febag.diff_spec_weak _ _ _ _ Ht).
      } 
    * rewrite Febag.empty_spec_weak in Ht; discriminate Ht.
  + rewrite eval_sql_query_unfold in Ht; cbv beta iota zeta in Ht.
    rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ht. 
    destruct Ht as [t' [Ht Ht']].
    rewrite in_map_iff in Ht'.
    destruct Ht' as [st [Ht' Hst]].
    subst t'.
    rewrite (Fset.equal_eq_1 _ _ _ _ (tuple_eq_labels _ _ _ Ht)).
    destruct s as [ | [s]];
      [ | rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)), sql_sort_unfold, map_map;
          unfold select_as_as_pair; apply Fset.equal_refl_alt; apply f_equal;
          rewrite <- map_eq; intros [] _; apply refl_equal].
    rewrite filter_In in Hst; destruct Hst as [Hst _]; destruct gby as [gby | ]; simpl in Hst.
    * assert (Jst := in_map_snd_partition_diff_nil _ _ _ Hst); simpl.
      assert (Lst := length_quicksort (OTuple T) st).
      case_eq (quicksort (OTuple T) st); [intro Q | intros u1 l1 Q]; rewrite Q in Lst; 
        [destruct st; [apply False_rec; apply Jst; apply refl_equal | discriminate Lst] | ].
      assert (Hu1 : In u1 st).
      {
        rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
      }
      assert (Kst := Oeset.in_mem_bool (OTuple T) _ _ (in_map_snd_partition _ _ _ _ _ Hst Hu1)).
      rewrite <- Febag.mem_unfold, Febag.mem_filter, Bool.Bool.andb_true_iff in Kst.
      -- destruct Kst as [Kst _].
        apply (proj2 IHn) with env; [sql_size_tac | assumption].
      -- intros x1 x2 Hx1 Hx; apply f_equal; apply eval_sql_formula_eq; env_tac.
    * rewrite in_map_iff in Hst; destruct Hst as [_st [_Hst Hst]]; subst st; simpl.
      apply (proj2 IHn) with env; [sql_size_tac | ].
      assert (Kst := Oeset.in_mem_bool (OTuple T) _ _ Hst).
      rewrite <- Febag.mem_unfold, Febag.mem_filter, Bool.Bool.andb_true_iff in Kst.
      -- apply (proj1 Kst).
      -- intros x1 x2 Hx1 Hx; apply f_equal; apply eval_sql_formula_eq; env_tac.
- assert (IH : forall f : sql_from_item,
                tree_size (tree_of_sql_from_item f) <= S n ->
                forall t env, t inBE (eval_sql_from_item env f) -> 
                              labels T t =S= (sql_from_item_sort f)).
  {
    intros f Hn t env Ht; destruct f as [s [ | rho]].
    - simpl; apply (proj1 IHn) with env; [sql_size_tac | ].
      simpl in Ht; unfold Febag.map in Ht.
      rewrite Febag.mem_mk_bag, map_id, Oeset.mem_bool_true_iff in Ht; trivial.
      destruct Ht as [t' [Ht Ht']].
      rewrite (Febag.mem_eq_1 _ _ _ _ Ht); apply Febag.in_elements_mem; assumption.
    - rewrite eval_sql_from_item_unfold, Febag.mem_map in Ht.
      destruct Ht as [t' [Ht Ht']].
      simpl att_renaming_item_to_from_item in Ht.
      rewrite (Fset.equal_eq_1 _ _ _ _ (tuple_eq_labels _ _ _ Ht)),
        (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)), sql_from_item_sort_unfold.
      unfold att_as_as_pair; rewrite !map_map.
      rewrite Fset.equal_spec; intro a; do 2 apply f_equal.
      rewrite <- map_eq; intros [] _; trivial.
      }
  intros lf Hn t env Ht.
  unfold N_join_bag in Ht.
  rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in Ht.
  destruct Ht as [t' [Ht Ht']].
  rewrite tuple_eq in Ht; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ht)); clear Ht.
  rewrite in_N_join_list in Ht'.
  destruct Ht' as [llt [H1 [H2 H3]]]; subst t'.
  rewrite map_map in H2.
  assert (H3 : labels T (N_join tuple (join_tuple T) (empty_tuple T) (map snd llt)) =S=
               Fset.Union (A T) (map (labels T) (map snd llt))).
  {
    clear H1 H2; set (l := map snd llt); clearbody l; clear llt.
    induction l as [ | t1 l]; simpl.
    - unfold empty_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.equal_refl.
    - unfold join_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.union_eq_2; apply IHl.
  }
  rewrite (Fset.equal_eq_1 _ _ _ _ H3), map_map; clear H3.
  revert llt H1 H2; induction lf as [ | f1 lf]; intros llt H1 H2.
  + destruct llt; [ | discriminate H2].
    apply Fset.equal_refl.
  + destruct llt as [ | [l1 t1] llt]; [discriminate H2 | ].
    simpl in H2; injection H2; clear H2; intros H2 H3; simpl map.
    rewrite 2 (Fset.Union_unfold _ (_ :: _)).
    apply Fset.union_eq.
    * apply IH with env; 
        [refine (le_trans _ _ _ _ Hn);
         apply in_list_size; rewrite in_map_iff; exists f1; split; [ | left]; trivial | ].
      rewrite Febag.mem_unfold; apply Oeset.in_mem_bool.
      apply H1; left; apply f_equal2; trivial.
    * apply IHlf; 
        [refine (le_trans _ _ _ _ Hn); simpl; apply le_plus_r | intros; apply H1; right | ]; 
        trivial.
Qed.

Lemma well_sorted_sql_query :
  well_sorted_sql_table -> 
  forall sq t env, t inBE (eval_sql_query env sq) -> labels T t =S= sql_sort sq.
Proof.
intros W sq.
apply (proj1 (well_sorted_sql_query_etc W (tree_size (tree_of_sql_query sq)))).
apply le_n.
Qed.

Lemma well_sorted_sql_from_item :
  well_sorted_sql_table ->
  forall x t env, t inBE (eval_sql_from_item env x) -> labels T t =S= sql_from_item_sort x.
Proof.
intros W [sq r] t env H; rewrite eval_sql_from_item_unfold, Febag.map_unfold in H.
rewrite Febag.mem_mk_bag, Oeset.mem_bool_true_iff in H.
destruct H as [t' [Ht H]]; rewrite in_map_iff in H.
destruct H as [t'' [H Ht'']]; subst t'.
rewrite tuple_eq in Ht; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ht)).
assert (Wt'' := well_sorted_sql_query W _ _ _ (Febag.in_elements_mem _ _ _ Ht'')).
destruct r as [ | r].
- simpl projection; rewrite (Fset.equal_eq_1 _ _ _ _ Wt''); simpl.
  apply Fset.equal_refl.
- simpl att_renaming_item_to_from_item; 
    rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _ _)), sql_from_item_sort_unfold.
  unfold att_as_as_pair; rewrite !map_map.
  rewrite Fset.equal_spec; intro a; do 2 apply f_equal.
  rewrite <- map_eq.
  intros [] _; apply refl_equal.
Qed.

Lemma projection_id :
 forall env esq sa, 
   (forall t, In t esq -> labels T t =S= sa) ->
   let p := (partition (mk_olists (OVal T))
            (fun t0 : tuple =>
             map (fun f  => interp_aggterm T (env_t T env t0) f)
               (map (fun a : attribute => A_Expr (F_Dot a)) ({{{sa}}}))) esq) in
  forall x v l, In (v, l) p -> In x l ->
        projection T
          (env_g T env (Group_By (map (fun a : attribute => A_Expr (F_Dot a)) ({{{sa}}}))) l)
          (Select_List (_Select_List (id_renaming T sa))) =t= x.
Proof.
intros env esq sa W p x v l Hl Hx; unfold p in *.
assert (Wx := W x (in_partition _ _ _ _ _ _ Hl Hx)).
assert (K : forall y, In y l -> y =t= x).
{
  intros y Hy.
  assert (Wy := W y (in_partition _ _ _ _ _ _ Hl Hy)).
  rewrite tuple_eq, Fset.equal_spec; split.
  - rewrite Fset.equal_spec in Wx, Wy; intro; rewrite Wx, Wy; apply refl_equal.
  - intros a Ha.
    rewrite (Fset.mem_eq_2 _ _ _ Wy) in Ha.
    assert (H := partition_homogeneous_values _ _ _ _ _ Hl _ Hy).
    rewrite <- (partition_homogeneous_values _ _ _ _ _ Hl _ Hx) in H.
    rewrite !map_map, <- map_eq in H.
    assert (Ka := H a); simpl in Ka.
    rewrite (Fset.mem_eq_2 _ _ _ Wx), (Fset.mem_eq_2 _ _ _ Wy), Ha in Ka.
    apply Ka; apply Fset.mem_in_elements; assumption.
}
unfold id_renaming, pair_of_select; simpl; rewrite !map_map, map_id; [ | intros; apply refl_equal].
rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
  (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_idem _ _)), (Fset.equal_eq_2 _ _ _ _ Wx); split;
  [apply Fset.equal_refl | ].
intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
rewrite dot_mk_tuple, Ha; unfold pair_of_select.
rewrite Oset.find_map; [ | rewrite  Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha; apply Ha].
rewrite (Fset.mem_eq_2 _ _ _ (Fset.mk_set_idem _ _)) in Ha.
simpl.
rewrite (In_quicksort (OTuple T)) in Hx.
case_eq (quicksort (OTuple T) l); [intro Q; rewrite Q in Hx; contradiction Hx | ].
intros x1 q1 Q.
assert (Hx1 : x1 =t= x).
{
  apply K; rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
}
rewrite tuple_eq in Hx1.
rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)), (Fset.mem_eq_2 _ _ _ Wx), Ha.
apply (proj2 Hx1).
rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)), (Fset.mem_eq_2 _ _ _ Wx), Ha; apply refl_equal.
Qed.

Lemma nb_occ_join_tuple_N_product_bag :
  forall t s1 s2 l1 l2,
    Fset.is_empty _ (Fset.inter _ s1 s2) = true ->
    labels T t =S= Fset.union _ s1 s2 -> 
    (forall t, Febag.mem _ t l1 = true -> labels T t =S= s1) -> 
    (forall t, Febag.mem _ t l2 = true -> labels T t =S= s2) -> 
        (Febag.nb_occ BTupleT t (N_join_bag T (l1 :: l2 :: nil))) =
        ((Febag.nb_occ BTupleT (mk_tuple T s1 (fun a => dot T t a)) l1) * 
         (Febag.nb_occ BTupleT (mk_tuple T s2 (fun a => dot T t a)) l2))%N.
Proof.
intros t s1 s2 _l1 _l2 Hq Ht _Hl1 _Hl2.
unfold N_join_bag; rewrite Febag.nb_occ_mk_bag, !map_unfold, N_join_list_unfold.
unfold brute_left_join_list, theta_join_list, d_join_list.
rewrite filter_true; [ | intros; apply refl_equal].
simpl.
rewrite 2 Febag.nb_occ_elements.
set (l1 := Febag.elements BTupleT _l1).
set (l2 := Febag.elements BTupleT _l2).
assert (Hl1 : 
          forall t, Oeset.mem_bool (OTuple T) t l1 = true -> labels T t =S= s1).
{
  intro _t; unfold l1; intro _Ht.
  apply _Hl1.
  rewrite Febag.mem_unfold; apply _Ht.
}
assert (Hl2 : 
          forall t, Oeset.mem_bool (OTuple T) t l2 = true -> labels T t =S= s2).
{
  intro _t; unfold l2; intro _Ht.
  apply _Hl2.
  rewrite Febag.mem_unfold; apply _Ht.
}
clearbody l1 l2; clear _l1 _l2 _Hl1 _Hl2.
unfold brute_left_join_list, theta_join_list, d_join_list; simpl.
revert l2 Hl2; induction l1 as [ | a1 l1]; intros l2 Hl2; [apply refl_equal | simpl].
rewrite map_flat_map, Oeset.nb_occ_app, IHl1, N.mul_add_distr_r.
- apply f_equal2; [ | apply refl_equal].
  induction l2 as [ | a2 l2]; [simpl; rewrite N.mul_0_r; apply refl_equal | ].
  rewrite flat_map_unfold, Oeset.nb_occ_app, 
  (Oeset.nb_occ_unfold _ _ (_ :: _)), N.mul_add_distr_l.
  apply f_equal2; [ | apply IHl2].
  + rewrite !map_unfold, !Oeset.nb_occ_unfold, N.add_0_r.
    rewrite (Oeset.compare_eq_2 _ _ _ _ (join_tuple_assoc _ _ _ _)).
    rewrite (Oeset.compare_eq_2 _ _ _ _ (join_tuple_empty_2 _ _)).
    assert (K1 : labels T a1 =S= s1).
    {
      apply Hl1; rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl.
      apply refl_equal.
    }
    assert (K2 : labels T a2 =S= s2).
    {
      apply Hl2; rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl.
      apply refl_equal.
    }
    assert (Hj : join_compatible_tuple T a1 a2 = true).
    {
      rewrite join_compatible_tuple_alt.
      intros a H1 H2.
      assert (Ha : Fset.mem (A T) a (Fset.empty _) = true).
      {
        rewrite Fset.is_empty_spec, Fset.equal_spec in Hq.
        rewrite <- Hq, Fset.mem_inter, <- (Fset.mem_eq_2 _ _ _ K1), H1.
        rewrite <- (Fset.mem_eq_2 _ _ _ K2), H2; apply refl_equal.
      }
      rewrite Fset.empty_spec in Ha; discriminate Ha.
    }
    case_eq (Oeset.compare (OTuple T) t (join_tuple T a1 a2)); intro Kt.
    * rewrite (split_tuple T _ _ t _ _ K1 K2 Hj) in Kt; destruct Kt as [Kt1 [Kt2 Kt]].
      rewrite (Oeset.compare_eq_2 _ _ _ _ Kt1), Oeset.compare_eq_refl.
      rewrite (Oeset.compare_eq_2 _ _ _ _ Kt2), Oeset.compare_eq_refl.
      apply refl_equal.
    * case_eq 
        (Oeset.compare (OTuple T) 
                       (mk_tuple T s1 (fun a : attribute => dot T t a)) a1); 
        intro H1; try (rewrite N.mul_0_l; apply refl_equal).
      case_eq 
        (Oeset.compare (OTuple T) 
                       (mk_tuple T s2 (fun a : attribute => dot T t a)) a2);
        intro H2; try (rewrite N.mul_0_r; apply refl_equal).
      apply False_rec.
      assert (Kt' : Oeset.compare  (OTuple T) t (join_tuple T a1 a2) = Eq).
      {
        rewrite (split_tuple T _ _ t _ _ K1 K2 Hj).
        split; [rewrite (Oeset.compare_eq_2 _ _ _ _ H1); apply Oeset.compare_eq_refl | ].
        split; [rewrite (Oeset.compare_eq_2 _ _ _ _ H2); apply Oeset.compare_eq_refl | ].
        assumption.
      }
      rewrite <- (Oeset.compare_eq_2 _ _ _ _ Kt'), Oeset.compare_eq_refl in Kt; discriminate Kt.
    * case_eq 
        (Oeset.compare (OTuple T) 
                       (mk_tuple T s1 (fun a : attribute => dot T t a)) a1); 
        intro H1; try (rewrite N.mul_0_l; apply refl_equal).
      case_eq 
        (Oeset.compare (OTuple T) 
                       (mk_tuple T s2 (fun a : attribute => dot T t a)) a2);
        intro H2; try (rewrite N.mul_0_r; apply refl_equal).
      apply False_rec.
      assert (Kt' : Oeset.compare  (OTuple T) t (join_tuple T a1 a2) = Eq).
      {
        rewrite (split_tuple T _ _ t _ _ K1 K2 Hj).
        split; [rewrite (Oeset.compare_eq_2 _ _ _ _ H1); apply Oeset.compare_eq_refl | ].
        split; [rewrite (Oeset.compare_eq_2 _ _ _ _ H2); apply Oeset.compare_eq_refl | ].
        assumption.
      }
      rewrite <- (Oeset.compare_eq_2 _ _ _ _ Kt'), Oeset.compare_eq_refl in Kt; discriminate Kt.
  + intros t2 Ht2; apply Hl2; rewrite Oeset.mem_bool_unfold, Ht2, Bool.orb_true_r.
    apply refl_equal.
- intros t1 Ht1; apply Hl1; rewrite Oeset.mem_bool_unfold, Ht1, Bool.orb_true_r.
  apply refl_equal.
- intros t2 Ht2; apply Hl2; assumption.
Qed.

Definition delta (sq : sql_query) :=
  let s := sql_sort sq in 
  let ss := id_renaming T s in
  Sql_Select 
    (Select_List (_Select_List ss))
    (From_Item sq Att_Ren_Star :: nil) 
    (Sql_True _)
    (Group_By (map (fun a => A_Expr (F_Dot a)) (Fset.elements _ s)))
    (Sql_True _).



Lemma delta_is_distinct :
  well_sorted_sql_table ->
  forall env sq t, Febag.nb_occ _ t (eval_sql_query env (delta sq)) =
                   N.min 1 (Febag.nb_occ _ t (eval_sql_query env sq)).
Proof.
intros WI env sq t; unfold delta.
rewrite eval_sql_query_unfold; cbv beta iota zeta.
assert (Hb := refl_equal (Bool.true (B T))).
rewrite <- Bool.true_is_true in Hb.
simpl eval_sql_formula; rewrite Hb, filter_true; [ | intros; apply refl_equal].
rewrite Febag.nb_occ_mk_bag.
apply eq_trans with
(Oeset.nb_occ (OTuple T) t
    (map
       (fun g : list tuple =>
        projection T
          (env_g T env (Group_By (map (fun a => A_Expr (F_Dot a)) ({{{sql_sort sq}}}))) g)
          (Select_List (_Select_List (id_renaming T (sql_sort sq)))))
       (FlatData.make_groups T env
          (Febag.elements BTupleT (eval_sql_query env sq))
          (Group_By (map (fun a => A_Expr (F_Dot a)) ({{{sql_sort sq}}})))))).
- apply Oeset.nb_occ_map_eq_2_3 with (OLTuple T).
  + intros; apply projection_eq; env_tac.
  + intro l; apply Oeset.permut_nb_occ; unfold FlatData.make_groups.
    apply _permut_map with 
        (fun x y => Oeset.compare (VOLA (OTuple T) (mk_olists (OVal T))) x y = Eq).
    * intros [a1 a2] [b1 b2] _ _; simpl.
      case ( comparelA (Oset.compare (OVal T)) a1 b1); try discriminate.
      exact (fun h => h).
    * apply partition_eq_2.
      -- intros x Hx x' Hx'; rewrite !map_map, <- map_eq.
         intros a Ha; apply interp_funterm_eq; env_tac.
      -- apply Oeset.nb_occ_permut; intro x.
         rewrite <- !Febag.nb_occ_elements, Febag.nb_occ_filter; [ | intros; apply refl_equal].
         rewrite N.mul_1_r, (map_unfold _ (_ :: _)), (map_unfold _ nil), N_join_bag_1; simpl.
         unfold Febag.map; rewrite Febag.nb_occ_mk_bag, map_id; [ | intros; apply refl_equal].
         rewrite Febag.nb_occ_elements; apply refl_equal.
- unfold FlatData.make_groups; rewrite Febag.nb_occ_elements.
  set (esq := Febag.elements BTupleT (eval_sql_query env sq)).
  set (f := (fun t0 : tuple =>
              map (fun f : aggterm => interp_aggterm T (env_t T env t0) f)
                (map (fun a : attribute => A_Expr (F_Dot a)) ({{{sql_sort sq}}})))).
  apply eq_trans with
      (Oeset.nb_occ 
         (OTuple T) t
         (map (fun g : list tuple => match g with nil => t | u :: _ => u end)
            (map snd (partition (mk_olists (OVal T)) f esq)))).
  + apply (Oeset.nb_occ_map_eq_2_alt (OLTuple T)).
    intros l Hl;rewrite in_map_iff in Hl; destruct Hl as [[v _l] [_Hl Hl]]; simpl in _Hl; subst _l.
    assert (H := in_partition_diff_nil _ _ _ _ Hl).
    destruct l as [ | u l]; [apply False_rec; apply H; apply refl_equal | ].
    apply projection_id with esq v.
    * intros x Hx; apply (well_sorted_sql_query WI sq x) with env.
      apply Febag.in_elements_mem; apply Hx.
    * assumption.
    * left; apply refl_equal.
  + rewrite Oeset.all_diff_bool_nb_occ_mem.
    * case_eq (Oeset.mem_bool (OTuple T) t
      (map (fun g : list tuple => match g with
                                  | nil => t
                                  | u :: _ => u
                                  end) (map snd (partition (mk_olists (OVal T)) f esq)))).
      -- intro Ht; rewrite Oeset.mem_bool_true_iff in Ht.
         destruct Ht as [t' [Ht Ht']].
         rewrite map_map, in_map_iff in Ht'; destruct Ht' as [[v l] [H1 H2]]; simpl in H1.
         destruct l as [ | u l];
           [apply False_rec; apply (in_partition_diff_nil _ f esq _ H2); 
            apply refl_equal | subst t'].
         assert (H3 := 
                   Oeset.in_mem_bool 
                     (OTuple T) _ _ (in_partition _ _ _ _ _ u H2 (or_introl _ (refl_equal _)))).
         rewrite <- (Oeset.mem_bool_eq_1 _ _ _ _ Ht) in H3.
         assert (H4 := Oeset.mem_nb_occ _ _ _ H3).
         destruct (Oeset.nb_occ (OTuple T) t esq) as [ | p]; 
           [apply False_rec; apply H4; apply refl_equal | destruct p; trivial].
      -- intro Ht.
         case_eq ((Oeset.nb_occ (OTuple T) t esq)); [intros; apply refl_equal | ].
         intros p Hp.
         rewrite <- Bool.not_true_iff_false in Ht; apply False_rec; apply Ht.
         assert (H3 : Oeset.mem_bool (OTuple T) t esq = true).
         {
           apply Oeset.nb_occ_mem; rewrite Hp; discriminate.
         }
         rewrite Oeset.mem_bool_true_iff in H3.
         destruct H3 as [t' [_Ht Ht']]; rewrite (Oeset.mem_bool_eq_1 _ _ _ _ _Ht).
         rewrite (in_permut_in (partition_permut (mk_olists (OVal T)) f esq)) in Ht'.
         rewrite in_flat_map in Ht'.
         destruct Ht' as [[v l] [_Ht' Ht']].
         destruct l as [ | u l];
           [apply False_rec; apply (in_partition_diff_nil _ f esq _ _Ht'); apply refl_equal | ].
         assert (Hu : t' =t= u).
         {
           assert (W : (forall t : tuple, In t esq -> labels T t =S= sql_sort sq)).
           {
             intros x Hx; apply (well_sorted_sql_query WI sq x) with env.
             rewrite Febag.mem_unfold; apply Oeset.in_mem_bool; assumption.
           }
           rewrite <- (Oeset.compare_eq_2 
                        _ _ _ _
                        (projection_id env esq (sql_sort sq) W u v (u :: l) _Ht' 
                                       (or_introl _ (refl_equal _)))).
           rewrite <- (Oeset.compare_eq_1 
                        _ _ _ _
                        (projection_id env esq (sql_sort sq) W t' v (u :: l) _Ht' Ht')).
           apply Oeset.compare_eq_refl.
         }
         rewrite (Oeset.mem_bool_eq_1 _ _ _ _ Hu).
         apply Oeset.in_mem_bool; rewrite map_map, in_map_iff.
         eexists; split; [ | apply _Ht']; apply refl_equal.
    * rewrite map_map.
      case_eq (Oeset.all_diff_bool 
                 (OTuple T)
                 (map (fun x : list value * list tuple => match snd x with
                                                          | nil => t
                                                          | u :: _ => u
                                                          end) 
                      (partition (mk_olists (OVal T)) f esq))); intro H; [apply refl_equal | ].
      destruct (Oeset.all_diff_bool_false _ _ H) as [t1 [t2 [p1 [p2 [p3 [H1 H2]]]]]].
      destruct (map_app_alt _ _ _ _ H2) as [pp1 [pp [Hesq [Hp1 _Hpp]]]]; clear H2.
      destruct pp as [ | [v1 l1] pp]; [discriminate _Hpp | ].
      simpl in _Hpp; injection _Hpp; clear _Hpp; intros _Hpp Hl1.
      destruct (map_app_alt _ _ _ _ _Hpp) as [pp2 [pp3 [K4 [Hp2 Hpp]]]]; clear _Hpp.
      destruct pp3 as [ | [v2 l2] pp3]; [discriminate Hpp | ].
      simpl in Hpp; injection Hpp; clear Hpp; intros Hp3 Hl2.
      rewrite K4 in Hesq.
      assert (Kl1 : l1 <> nil).
      {
        apply (in_partition_diff_nil (mk_olists (OVal T)) f esq v1).
        rewrite Hesq; apply in_or_app; right; left; apply refl_equal.
      }
      destruct l1 as [ | u1 l1]; [apply False_rec; apply Kl1; apply refl_equal | ].
      assert (Kl2 : l2 <> nil).
      {
        apply (in_partition_diff_nil (mk_olists (OVal T)) f esq v2).
        rewrite Hesq; apply in_or_app; do 2 right.
        apply in_or_app; right; left; apply refl_equal.
      }
      destruct l2 as [ | u2 l2]; [apply False_rec; apply Kl2; apply refl_equal | ].
      clear Kl1 Kl2; subst u1 u2.
      assert (Ht1 : f t1 = v1).
      {
        apply (partition_homogeneous_values (mk_olists (OVal T)) f esq) with (t1 :: l1).
        - rewrite Hesq; apply in_or_app; right; left; apply refl_equal.
        - left; apply refl_equal.
      }
      assert (Ht2 : f t2 = v2).
      {
        apply (partition_homogeneous_values (mk_olists (OVal T)) f esq) with (t2 :: l2).
        - rewrite Hesq; apply in_or_app; do 2 right.
          apply in_or_app; right; left; apply refl_equal.
        - left; apply refl_equal.
      }
      assert (Hv : v1 = v2).
      {
        rewrite <- Ht1, <- Ht2.
        unfold f; rewrite !map_map, <- map_eq.
        intros a Ha; apply interp_funterm_eq; env_tac.
      }
      assert (Abs := partition_all_diff_values (mk_olists (OVal T)) f esq).
      rewrite Hesq, map_app, (map_unfold _ (_ :: _)), map_app, (map_unfold _ (_ :: _)) in Abs.
      rewrite <- all_diff_app_iff in Abs; destruct Abs as [_ [Abs _]].
      rewrite all_diff_unfold in Abs; destruct Abs as [Abs _].
      apply False_rec.
      refine (Abs v2 _ Hv); apply in_or_app; right; left; apply refl_equal.
Qed.

(*
Definition equiv_abstract_env_slice (e1 e2 : (Fset.set (A T) * group_by T)) := 
  match e1, e2 with
    | (sa1, g1), (sa2, g2) => 
      sa1 =S= sa2 /\ g1 = g2 
  end.

Lemma equiv_abstract_env_slice_sym :
  forall e1 e2, 
    equiv_abstract_env_slice e1 e2 <-> equiv_abstract_env_slice e2 e1.
Proof.
Proof.
intros [sa1 g1] [sa2 g2]; split; intros [H1 H2]; simpl; repeat split.
- rewrite Fset.equal_spec in H1; rewrite Fset.equal_spec; intro; rewrite H1; trivial.
- subst; trivial.
- rewrite Fset.equal_spec in H1; rewrite Fset.equal_spec; intro; rewrite H1; trivial.
- subst; trivial.
Qed.

Lemma env_g_fine_eq_2 :
  forall e x1 x2, 
    x1 =t= x2 -> 
    equiv_env T (env_g T e Group_Fine (x1 :: nil)) (env_g T e Group_Fine (x2 :: nil)).
Proof.
intros e x1 x2 Hx.
constructor 2.
- simpl; repeat split.
  + rewrite tuple_eq in Hx; apply (proj1 Hx).
  + simpl; apply compare_list_t; unfold compare_OLA; simpl.
    rewrite Hx; apply refl_equal.
- apply equiv_env_refl.
Qed.

Lemma env_g_eq_2 :
  forall e g x1 x2, 
    Oeset.compare (OLTuple T) x1 x2 = Eq ->
    equiv_env T (env_g T e g x1) (env_g T e g x2).
Proof.
intros e g x1 x2 Hx.
Locate equiv_env.
Locate env_t.
unfold env_g; rewrite equiv_env_unfold.
 constructor 2; [ | apply equiv_env_refl].

      simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption

constructor 2.
- simpl; repeat split.
  + rewrite tuple_eq in Hx; apply (proj1 Hx).
  + simpl; apply compare_list_t; unfold compare_OLA; simpl.
    rewrite Hx; apply refl_equal.
- apply equiv_env_refl.
Qed.


Ltac env_tac :=
  match goal with
    | |- equiv_env _ ?e ?e => apply equiv_abstract_env_refl

(* env_g *)
    | Hx : ?x1 =t= ?x2 
      |- equiv_env _ (env_g _ ?e Group_Fine (?x1 :: nil)) 
                   (env_g _ ?e Group_Fine (?x2 :: nil)) =>
      apply env_g_fine_eq_2; assumption

    | Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ (env_g _ ?e ?g ?x1) (env_g _ ?e ?g ?x2) =>
      unfold env_g; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption

    | He : equiv_env _ ?e1 ?e2
      |- equiv_env _ (env_g _ ?e1 ?g ?x) (env_g _ ?e2 ?g ?x) =>
      unfold env_g; constructor 2; [ | apply He];
      simpl; repeat split; trivial;
      [apply Fset.equal_refl | apply Oeset.permut_refl]

    | He : equiv_env _ ?e1 ?e2, 
      Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ (env_g _ ?e1 ?g ?x1) (env_g _ ?e2 ?g ?x2) =>
      unfold env_g; constructor 2; [ | apply He];
      simpl; repeat split; 
      [apply env_slice_eq_1 | rewrite compare_list_t]; assumption

(* env_t *)
    | Hx : ?x1 =t= ?x2 
      |- equiv_env _ (env_t _ ?env ?x1) (env_t _ ?env ?x2) =>
      unfold env_t; constructor 2; [ | apply equiv_env_refl];
      simpl; repeat split; [ | apply compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

    | He : equiv_env _ ?env1 ?env2, Hx : ?x1 =t= ?x2 
      |- equiv_env _ (env_t _ ?env1 ?x1) (env_t _ ?env2 ?x2) =>
      unfold env_t; constructor 2; [ | assumption];
      simpl; repeat split; [rewrite tuple_eq in Hx; apply (proj1 Hx) | ];
      apply Oeset.permut_cons; [assumption | apply Oeset.permut_refl]

(* env_t, env_g *)
    | He : equiv_env _ ?e1 ?e2, Hx : ?x1 =t= ?x2
      |- equiv_env _ (env_t _ ?e1 ?x1) (env_g _ ?e2 Group_Fine (?x2 :: nil)) =>
      unfold env_t, env_g; constructor 2; [ | apply He];
      simpl; repeat split; [ | rewrite compare_list_t; simpl; rewrite Hx; trivial];
      rewrite tuple_eq in Hx; apply (proj1 Hx)

    | He : equiv_env _ ?e1 ?e2
      |- equiv_env _ (env_t _ ?e1 ?x) (env_g _ ?e2 Group_Fine (?x :: nil)) =>
      unfold env_t, env_g; constructor 2; [ | apply He];
      simpl; repeat split; 
      [apply Fset.equal_refl | rewrite compare_list_t; simpl; rewrite Oeset.compare_eq_refl; trivial]

(* env *)
    | He : equiv_env _ ?e1 ?e2
      |- equiv_env _ ((?sa1, ?g, ?x) :: ?e1) ((?sa1, ?g, ?x) :: ?e2) =>
      constructor 2; [ | assumption];
      simpl; repeat split; trivial;
      [apply Fset.equal_refl | 
       rewrite compare_list_t; apply Oeset.compare_eq_refl]

    |  Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ ((?sa1, ?g, ?x1) :: ?e1) ((?sa1, ?g, ?x2) :: ?e1) =>
       constructor 2; [ | apply equiv_env_refl];
       simpl; repeat split; [apply Fset.equal_refl | rewrite compare_list_t; assumption] 

    |  Hx : Oeset.compare (OTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ ((?sa, ?g, ?x1 :: nil) :: ?e) ((?sa, ?g, ?x2 :: ?nil) :: ?e) =>
       constructor 2; [ | apply equiv_env_refl];
       simpl; repeat split; 
       [apply Fset.equal_refl | rewrite compare_list_t; simpl; rewrite Hx; trivial]

    | He : equiv_env _ ?e1 ?e2,
           Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ ((?sa1, ?g, ?x1) :: ?e1) ((?sa1, ?g, ?x2) :: ?e2) =>
      constructor 2; [ | apply He];
      simpl; repeat split; 
      [apply Fset.equal_refl | rewrite compare_list_t; assumption]

    | He : equiv_env _ ?e1 ?e2,
           Hx : Oeset.compare (OTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ ((?sa, ?g, ?x1 :: nil) :: ?e1) ((?sa, ?g, ?x2 :: ?nil) :: ?e2) =>
      constructor 2; [ | apply He]; 
      simpl; repeat split; 
      [apply Fset.equal_refl 
      | rewrite compare_list_t; simpl; rewrite Hx; trivial]
            
    | He : equiv_env _ ?e1 ?e2,
           Hx : Oeset.compare (OLTuple T) ?x1 ?x2 = Eq
      |- equiv_env _ ((?sa, ?g, ?x1) :: ?e1) (((?sa unionS (emptysetS)), ?g, ?x2) :: ?e2) => 
      constructor 2; [ | apply He];
      simpl; repeat split; 
      [ rewrite Fset.equal_spec; intro a;
        rewrite Fset.mem_union, Fset.empty_spec, Bool.orb_false_r; apply refl_equal
      | apply compare_list_t; trivial]

    | _ => trivial
  end.





Lemma interp_funterm_eq_ :
  forall env gby e, 
    In e (map (fun (f : funterm) (t : tuple) => interp_funterm (env_t T env t) f) gby) ->
    forall t1 t2 : tuple, t1 =t= t2 -> e t1 = e t2.
Proof.
intros env gby e He; rewrite in_map_iff in He.
destruct He as [f [He Hf]]; subst e.
intros t1 t2 Ht; apply interp_funterm_eq; env_tac.
Qed.



Lemma mk_tuple_id_alt :
  forall env g l sa, l <> nil ->
   (forall t, In t l -> labels T t =S= sa) ->
   projection T (env_g T env g l) Select_Star =t=
   projection T (env_g T env g l)
     (Select_List
        (map (fun a : attribute => Select_As T (A_Expr (F_Dot a)) a)
           ({{{sa}}}))).
Proof.
intros env g l sa H1 H2; unfold projection, env_g.
rewrite 3 map_map.
case_eq (quicksort (OTuple T) l).
- intro Hql.
  assert (Abs := length_quicksort (OTuple T) l).
  rewrite Hql in Abs; destruct l; [apply False_rec; apply H1; apply refl_equal | discriminate Abs].
- intros y1 ql Hql.
  destruct l as [ | x1 l1]; [apply False_rec; apply H1; apply refl_equal | ].
  rewrite tuple_eq, (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)), map_id; 
    [ | intros; apply refl_equal].
  rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.mk_set_idem _ _)).
  destruct l1 as [ | x2 l1]; split.
  + apply H2; left; apply refl_equal.
  + rewrite quicksort_equation in Hql; simpl in Hql; rewrite quicksort_equation in Hql.
    injection Hql; clear Hql; do 2 intro; subst y1 ql.
    intros a Ha.
    rewrite dot_mk_tuple, Fset.mem_mk_set, <- Fset.mem_elements.
    rewrite <- (Fset.mem_eq_2 _ _ _ (H2 x1 (or_introl _ (refl_equal _)))), Ha.
    rewrite Oset.find_map.
    * unfold interp_aggterm; simpl; rewrite Ha; apply refl_equal.
    * apply Fset.mem_in_elements.
      rewrite <- (Fset.mem_eq_2 _ _ _ (H2 x1 (or_introl _ (refl_equal _)))), Ha.
      apply refl_equal.
  + apply H2; apply (In_quicksort (OTuple T)).
    rewrite Hql; left; apply refl_equal.
  + intros a Ha. 
    rewrite dot_mk_tuple, Fset.mem_mk_set, <- Fset.mem_elements.
    assert (Ha' : (a inS? sa) = (a inS? labels T y1)).
    {
      apply sym_eq; apply Fset.mem_eq_2.
      apply H2; apply (In_quicksort (OTuple T)); rewrite Hql; left; trivial.
    }
    rewrite Ha', Ha, Oset.find_map.
    * unfold interp_aggterm; simpl; rewrite Hql, Ha; apply refl_equal.
    * apply Fset.mem_in_elements.
      rewrite Ha', Ha.
      apply refl_equal.
Qed.

*)



End Sec.


(** OCaml extraction (#<a href="eval_sql_query.ml">.ml</a>#, #<a href="eval_sql_query.mli">.mli</a>#) *)
(* Extraction "eval_sql_query.ml" eval_sql_query. *)
