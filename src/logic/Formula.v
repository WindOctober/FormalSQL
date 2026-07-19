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

Require Import Bool List NArith.
Require Import BasicFacts ListFacts Bool3 OrderedSet Tree FiniteSet ListPermut ListSort.

Inductive and_or : Type :=
  | And_F 
  | Or_F.

Register and_or as datacert.and_or.type.
Register And_F as datacert.and_or.And_F.
Register Or_F as datacert.and_or.Or_F.

Inductive quantifier : Type :=
  | Forall_F
  | Exists_F.

Register quantifier as datacert.quantifier.type.
Register Forall_F as datacert.quantifier.Forall_F.
Register Exists_F as datacert.quantifier.Exists_F.

(** Boolean connectives and quantifiers are shared by the SQL formula and
    query-expression semantics.  They require no ordering on syntax. *)
Section BooleanSemantics.

Hypothesis B : Bool.Rcd.

Definition interp_conj operation :=
  match operation with
  | And_F => Bool.andb B
  | Or_F => Bool.orb B
  end.

Definition interp_quant quantifier :=
  match quantifier with
  | Forall_F => Bool.forallb B
  | Exists_F => Bool.existsb B
  end.

End BooleanSemantics.

Section QuantifierCongruence.

Hypothesis B : Bool.Rcd.
Hypothesis value : Type.
Hypothesis OVal : Oeset.Rcd value.

Lemma interp_quant_eq :
  forall quantifier interpretation1 interpretation2 values1 values2,
    _permut
      (fun left right => Oeset.compare OVal left right = Eq)
      values1 values2 ->
    (forall left right,
       Oeset.mem_bool OVal left values1 = true ->
       Oeset.compare OVal left right = Eq ->
       interpretation1 left = interpretation2 right) ->
    interp_quant B quantifier interpretation1 values1 =
      interp_quant B quantifier interpretation2 values2.
Proof.
intros quantifier interpretation1 interpretation2 values1 values2 Hvalues Hinterp.
destruct quantifier; simpl interp_quant.
- apply (Bool.forallb_eq _ OVal); assumption.
- apply (Bool.existsb_eq _ OVal); assumption.
Qed.

End QuantifierCongruence.


Require Import FlatData FiniteCollection FiniteBag.

Import Tuple.

Section SQL.

Hypothesis T : Tuple.Rcd.

Hypothesis dom : Type.
Hypothesis attributes_of_dom : dom -> Fset.set (A T).

Notation attribute := (attribute T).
Notation predicate := (predicate T).
Notation tuple := (tuple T).
Notation aggterm := (aggterm T).
Notation select := (select T).
Notation group_by := (group_by T).
Arguments Select_As {T}.
Arguments Select_Star {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Notation B := (B T).
Notation interp_predicate := (interp_predicate T).
Notation interp_aggterm :=  (interp_aggterm T).
Notation projection := (projection T).

Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Arguments equiv_env {T}.

Inductive sql_formula : Type :=
  | Sql_Conj : and_or -> sql_formula -> sql_formula -> sql_formula 
  | Sql_Not : sql_formula -> sql_formula
  | Sql_True : sql_formula
  | Sql_Pred : predicate -> list aggterm -> sql_formula
  | Sql_Quant : quantifier -> predicate -> list aggterm -> dom -> sql_formula
  | Sql_In : list select -> dom -> sql_formula
  | Sql_Exists : dom -> sql_formula. 

Definition Sql_Conj_N a lf f0 :=
  fold_left (fun acc_f f => Sql_Conj a acc_f f) lf f0. 

Fixpoint attributes_sql_f (f : sql_formula) :=
  match f with
  | Sql_Conj _ f1 f2 => (attributes_sql_f f1) unionS (attributes_sql_f f2)
  | Sql_Not f => attributes_sql_f f
  | Sql_True => Fset.empty (A T)
  | Sql_Pred _ l => Fset.Union _ (List.map (variables_ag T) l)
  | Sql_Quant _ _ l q => Fset.Union _ (List.map (variables_ag T) l) unionS (attributes_of_dom q)
  | Sql_In l q => 
      Fset.Union _ (List.map (fun x => match x with 
                                         Select_As e _ => variables_ag T e
                                       end) l) unionS attributes_of_dom q
  | Sql_Exists q => attributes_of_dom q
  end.

Hypothesis unknown : Bool.b B.
Hypothesis contains_null : tuple -> bool.
Hypothesis contains_null_eq : forall t1 t2, t1 =t= t2 -> contains_null t1 = contains_null t2.

Hypothesis I : list (setA * group_by * list tuple) -> dom -> bagT.

Fixpoint eval_sql_formula env (f : sql_formula) : Bool.b B :=
  match f with
  | Sql_Conj a f1 f2 => (interp_conj B a) (eval_sql_formula env f1) (eval_sql_formula env f2)
  | Sql_Not f => Bool.negb B (eval_sql_formula env f)
  | Sql_True => Bool.true B
  | Sql_Pred p l => interp_predicate p (map (interp_aggterm env) l)
  | Sql_Quant qtf p l sq =>
    let lt := map (interp_aggterm env) l in
    interp_quant B qtf
                 (fun x => 
                    let la := Fset.elements _ (labels T x) in
                    interp_predicate p (lt ++ map (dot T x) la))
                 (Febag.elements _ (I env sq))
  | Sql_In s sq =>
      let p := (projection env (Select_List (_Select_List s))) in
      interp_quant 
        B Exists_F
        (fun x => match Oeset.compare (OTuple T) p x with 
                  | Eq => if contains_null p then unknown else Bool.true B 
                  | _ => if (contains_null p || contains_null x) then unknown else Bool.false B 
                  end)
        (Febag.elements _ (I env sq))                   
  | Sql_Exists sq =>
      if Febag.is_empty _ (I env sq) 
      then Bool.false B 
      else Bool.true B
  end.

Lemma eval_sql_formula_unfold :
  forall env f, eval_sql_formula env f =
  match f with
  | Sql_Conj a f1 f2 => (interp_conj B a) (eval_sql_formula env f1) (eval_sql_formula env f2)
  | Sql_Not f => Bool.negb B (eval_sql_formula env f)
  | Sql_True => Bool.true B
  | Sql_Pred p l => interp_predicate p (map (interp_aggterm env) l)
  | Sql_Quant qtf p l sq =>
    let lt := map (interp_aggterm env) l in
    interp_quant B qtf
                 (fun x => 
                    let la := Fset.elements _ (labels T x) in
                    interp_predicate p (lt ++ map (dot T x) la))
                 (Febag.elements _ (I env sq))
  | Sql_In s sq =>
      let p := (projection env (Select_List (_Select_List s))) in
      interp_quant 
        B Exists_F
        (fun x => match Oeset.compare (OTuple T) p x with 
                  | Eq => if contains_null p then unknown else Bool.true B 
                  | _ => if (contains_null p || contains_null x) then unknown else Bool.false B 
                  end)
        (Febag.elements _ (I env sq))                   
  | Sql_Exists sq =>
      if Febag.is_empty _ (I env sq) 
      then Bool.false B 
      else Bool.true B
  end.
Proof.
intros env f; case f; intros; apply refl_equal.
Qed.

Lemma eval_Sql_Conj_N_And_F :
  forall env lf f0, 
    eval_sql_formula env (Sql_Conj_N And_F lf f0) = Bool.true B <->
    (eval_sql_formula env f0 = Bool.true B /\ 
     (forall f, In f lf -> eval_sql_formula env f = Bool.true B)).
Proof.
intros env lf; induction lf as [ | f1 lf]; intros f0; split; simpl.
- intro H; split; [apply H | ].
  intros f Abs; contradiction Abs.
- intros [H _]; apply H.
- intro H; rewrite IHlf, eval_sql_formula_unfold in H; simpl interp_conj in H.
  rewrite Bool.andb_true_iff in H.
  split; [apply (proj1 (proj1 H)) | ].
  intros f [Hf | Hf].
  + subst f; apply (proj2 (proj1 H)).
  + apply (proj2 H); apply Hf.
- intros [Hf0 Hf]; rewrite IHlf, eval_sql_formula_unfold; simpl interp_conj.
  rewrite Bool.andb_true_iff.
  split; [ | intros; apply Hf; right; assumption].
  split; [apply Hf0 | ].
  apply Hf; left; apply refl_equal.
Qed.  

Hypothesis relname : Type.

Inductive All : Type :=
| All_relname : relname  -> All 
| All_attribute : attribute -> All
| All_predicate : predicate -> All
| All_aggterm : aggterm -> All.

Hypothesis tree_of_dom : dom -> tree All.

Definition tree_of_attribute (a : attribute) : tree All := Leaf (All_attribute a).

Definition tree_of_select s : tree All :=
  match s with
    | Select_As e a => Node 0 (Leaf (All_aggterm e) :: tree_of_attribute a :: nil)
  end.

Definition tree_of_select_item s : tree All :=
  match s with
    | Select_Star => Node 1 nil
    | Select_List (_Select_List s) => Node 2 (map tree_of_select s)
  end.

Fixpoint tree_of_sql_formula f : tree All :=
  match f with
    | Sql_Conj a f1 f2 =>
      Node
        (match a with And_F => 13 | Or_F => 14 end)
        (tree_of_sql_formula f1 :: tree_of_sql_formula f2 :: nil)
    | Sql_Not f => Node 15 (tree_of_sql_formula f :: nil)
    | Sql_True => Node 21 (Node 16 nil :: nil)
    | Sql_Pred p l =>
      Node 21 (Node 17 (Leaf (All_predicate p) :: map (fun x => Leaf (All_aggterm x)) l) :: nil)
    | Sql_Quant qf p l q =>
      Node 21 (Node
        (match qf with Forall_F => 18 | Exists_F => 19 end)
        (Leaf (All_predicate p) :: tree_of_dom q :: map (fun x => Leaf (All_aggterm x)) l) :: nil)
    | Sql_In s q =>
      Node 21 (Node 20 (tree_of_select_item (Select_List (_Select_List s)) :: tree_of_dom q :: nil) :: nil)
    | Sql_Exists q => Node 21 (Node 23 (tree_of_dom q :: nil) :: nil)
  end.

Lemma tree_of_sql_formula_unfold :
  forall f, tree_of_sql_formula f =
  match f with
    | Sql_Conj a f1 f2 =>
      Node
        (match a with And_F => 13 | Or_F => 14 end)
        (tree_of_sql_formula f1 :: tree_of_sql_formula f2 :: nil)
    | Sql_Not f => Node 15 (tree_of_sql_formula f :: nil)
    | Sql_True => Node 21 (Node 16 nil :: nil)
    | Sql_Pred p l =>
      Node 21 (Node 17 (Leaf (All_predicate p) :: map (fun x => Leaf (All_aggterm x)) l) :: nil)
    | Sql_Quant qf p l q =>
      Node 21 (Node
        (match qf with Forall_F => 18 | Exists_F => 19 end)
        (Leaf (All_predicate p) :: tree_of_dom q :: map (fun x => Leaf (All_aggterm x)) l) :: nil)
    | Sql_In s q =>
      Node 21 (Node 20 (tree_of_select_item (Select_List (_Select_List s)) :: tree_of_dom q :: nil) :: nil)
    | Sql_Exists q => Node 21 (Node 23 (tree_of_dom q :: nil) :: nil)
  end.
Proof.
intro f; case f; intros; apply refl_equal.
Qed.

Lemma size_of_formula_le_1 :
  forall f, tree_size (tree_of_sql_formula f) <= 1 -> False.
Proof.
intros f H; rewrite PeanoNat.Nat.le_1_r in H; destruct H as [H | H].
- destruct f as [o f1 f2 | f | | p l | qtf p l sq | s sq | sq]; simpl in H; discriminate H.
- destruct f as [o f1 f2 | f | | p l | qtf p l sq | s sq | sq]; simpl in H; try discriminate H.
  + destruct f1; simpl in H; inversion H.
  + destruct f; simpl in H; inversion H.
Qed.

Lemma tree_of_sql_formula_eq :
  forall n,
  (forall q1, tree_size (tree_of_dom q1) <= n ->
   forall q2, tree_of_dom q1 = tree_of_dom q2 -> q1 = q2) ->

  (forall f1, tree_size (tree_of_sql_formula f1) <= S n ->
      forall f2, tree_of_sql_formula f1 = tree_of_sql_formula f2 -> f1 = f2).
Proof.
intro n; induction n as [ | n].
- intros IHq f H.
  apply False_rec; apply (size_of_formula_le_1 _ H).
- intros IHq [[ | ] f11 f12 | f1 | | p1 l1 | [ | ] p1 l1 sq1 | s1 sq1 | sq1] Hn
         [[ | ] f21 f22 | f2 | | p2 l2 | [ | ] p2 l2 sq2 | s2 sq2 | sq2] H; 
  try discriminate H; trivial.
  + simpl in H; injection H; clear H; intros H2 H1.
    apply f_equal2.
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; apply Plus.le_plus_l.
        - assumption.
      }
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; refine (Le.le_trans _ _ _ _ (Plus.le_plus_r _ _)).
          apply Plus.le_plus_l.
        - assumption.
      }
  + simpl in H; injection H; clear H; intros H2 H1.
    apply f_equal2.
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; apply Plus.le_plus_l.
        - assumption.
      }
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; refine (Le.le_trans _ _ _ _ (Plus.le_plus_r _ _)).
          apply Plus.le_plus_l.
        - assumption.
      }
  + simpl in H; injection H; clear H; intro H.
    apply f_equal.
    apply IHn.
    * intros q Hq; apply IHq; apply le_S; assumption.
    * simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; apply Plus.le_plus_l.
    * assumption.
  + simpl in H; injection H; clear H; intros Hl Hp.
    apply f_equal2; [assumption | ].
    clear Hn; revert l2 Hl; 
      induction l1 as [ | x1 l1]; intros [ | x2 l2] Hl; try discriminate Hl; trivial.
    simpl in Hl; injection Hl; clear Hl; intros Hl Hx.
    apply f_equal2; [assumption | ].
    apply IHl1; assumption.
  + simpl in H; injection H; clear H; intros Hl Hs Hp.
    apply f_equal3; [assumption | | ].
    * clear Hn; revert l2 Hl; 
        induction l1 as [ | x1 l1]; intros [ | x2 l2] Hl; try discriminate Hl; trivial.
      simpl in Hl; injection Hl; clear Hl; intros Hl Hx.
      apply f_equal2; [assumption | ].
      apply IHl1; assumption.
    * apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      rewrite <- Plus.plus_assoc; apply Plus.le_plus_l.
  + simpl in H; injection H; clear H; intros Hl Hs Hp.
    apply f_equal3; [assumption | | ].
    * clear Hn; revert l2 Hl; 
        induction l1 as [ | x1 l1]; intros [ | x2 l2] Hl; try discriminate Hl; trivial.
      simpl in Hl; injection Hl; clear Hl; intros Hl Hx.
      apply f_equal2; [assumption | ].
      apply IHl1; assumption.
    * apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      rewrite <- Plus.plus_assoc; apply Plus.le_plus_l.
  + simpl in H; injection H; clear H; intros Hs Hl.
    apply f_equal2.
    * clear Hn; revert s2 Hl; 
        induction s1 as [ | x1 l1]; intros [ | x2 l2] Hl; try discriminate Hl; trivial.
      simpl in Hl; injection Hl; clear Hl; intros Hl Hx.
      apply f_equal2; [ | apply IHl1; assumption].
      destruct x1; destruct x2; simpl in Hx; injection Hx; clear Hx.
      intros; apply f_equal2; assumption.
    * apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      refine (Le.le_trans _ _ _ _ (Plus.le_plus_l _ _)).
      refine (Le.le_trans _ _ _ _ (Plus.le_plus_r _ _)).
      apply Plus.le_plus_l.
  + apply f_equal; simpl in H; injection H; clear H; intro H.
    apply IHq; [ | assumption].
    simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
    apply le_n_S; apply le_S.
    refine (Le.le_trans _ _ _ _ (Plus.le_plus_l _ _)).
    apply Plus.le_plus_l.
Qed.

Lemma eval_sql_formula_eq_etc :
  forall n,
    (forall q, tree_size (tree_of_dom q) <= n -> 
       forall env1 env2, equiv_env env1 env2 -> I env1 q =BE= I env2 q) ->
    forall f, tree_size (tree_of_sql_formula f) <= S n ->
       forall env1 env2, equiv_env env1 env2 -> eval_sql_formula env1 f = eval_sql_formula env2 f.
Proof.
intros n; induction n as [ | n].
- intros IHq f H.
  apply False_rec; apply (size_of_formula_le_1 _ H).
- intros IHq [o f1 f2 | f | | p l | qtf p l sq | s sq | sq] Hn env1 env2 He.
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_Conj _ _ _)).
    apply f_equal2.
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; apply Plus.le_plus_l.
        - assumption.
      }
    * {
        apply IHn.
        - intros q Hq; apply IHq; apply le_S; assumption.
        - simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
          apply le_n_S; refine (Le.le_trans _ _ _ _ (Plus.le_plus_r _ _)).
          apply Plus.le_plus_l.
        - assumption.
      }
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_Not _)).
    apply f_equal.
    apply IHn.
    * intros q Hq; apply IHq; apply le_S; assumption.
    * simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; apply Plus.le_plus_l.
    * assumption.
  + apply refl_equal.
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_Pred _ _)).
    apply f_equal; rewrite <- map_eq; intros x Hx.
    apply (interp_aggterm_eq T x _ _ He).
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_Quant _ _ _ _)).
    cbv beta iota zeta.
    apply (interp_quant_eq B (OTuple T)).
    * apply Oeset.nb_occ_permut.
      intro x; rewrite <- 2 Febag.nb_occ_elements; revert x; rewrite <- Febag.nb_occ_equal.
      apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      rewrite <- Plus.plus_assoc; apply Plus.le_plus_l.
    * intros x1 x2 Hx1 Hx; apply f_equal.
      {
        apply f_equal2.
        - rewrite <- map_eq; intros a Ha.
          apply (interp_aggterm_eq T a _ _ He).
        - rewrite tuple_eq in Hx.
          rewrite <- (Fset.elements_spec1 _ _ _ (proj1 Hx)), <- map_eq.
          intros; apply (proj2 Hx).
          apply Fset.in_elements_mem; assumption.
      } 
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_In _ _)).
    assert (IH : I env1 sq =BE= I env2 sq).
    {
      apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      refine (Le.le_trans _ _ _ _ (Plus.le_plus_l _ _)).
      refine (Le.le_trans _ _ _ _ (Plus.le_plus_r _ _)).
      apply Plus.le_plus_l.
    }
    assert (Aux := projection_eq T (Select_List (_Select_List s)) _ _ He).
    cbv beta iota zeta.
    apply (interp_quant_eq B (OTuple T)).
    * apply Oeset.nb_occ_permut.
      intro x; rewrite <- 2 Febag.nb_occ_elements; revert x; rewrite <- Febag.nb_occ_equal.
      apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; do 2 apply le_S.
      rewrite 2 Plus.plus_0_r.
      apply Plus.le_plus_r.
    * intros x1 x2 Hx1 Hx.
      rewrite <- (Oeset.compare_eq_2 _ _ _ _ Hx), <- (Oeset.compare_eq_1 _ _ _ _ Aux).
      rewrite <- (contains_null_eq _ _ Hx).
      rewrite <- (contains_null_eq _ _ Aux).
      apply refl_equal.
  + rewrite 2 (eval_sql_formula_unfold _ (Sql_Exists _)).
    apply if_eq.
    * rewrite 2 Febag.is_empty_spec.
      apply Febag.equal_eq_1.
      apply IHq; [ | assumption].
      simpl in Hn; apply le_S_n; refine (Le.le_trans _ _ _ _ Hn).
      apply le_n_S; apply le_S.
      refine (Le.le_trans _ _ _ _ (Plus.le_plus_l _ _)).
      apply Plus.le_plus_l.
    * intros; apply refl_equal.
    * intros; apply refl_equal.
Qed.

End SQL.
