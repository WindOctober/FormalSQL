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

Require Import Bool List Arith NArith.

Require Import BasicFacts ListFacts ListPermut ListSort OrderedSet 
        FiniteSet FiniteBag FiniteCollection.

Section Sec.

Hypotheses value attribute symb aggregate : Type.
Hypothesis OVal : Oset.Rcd value.
Hypothesis OAtt : Oset.Rcd attribute.
Hypothesis OSymb: Oset.Rcd symb.
Hypothesis OAggregate : Oset.Rcd aggregate.
Hypothesis A : Fset.Rcd OAtt.

Inductive funterm : Type :=
| F_Constant : value -> funterm
| F_Dot : attribute -> funterm
| F_Expr : symb -> list funterm -> funterm.

Inductive aggterm : Type := 
| A_Expr : funterm -> aggterm
| A_agg : aggregate -> funterm -> aggterm
| A_fun : symb -> list aggterm -> aggterm.

Fixpoint size_funterm (t : funterm) : nat :=
  match t with
    | F_Constant _
    | F_Dot _ => 1%nat
    | F_Expr _ l => S (list_size size_funterm l)
  end.

Fixpoint size_aggterm (t : aggterm) : nat :=
  match t with
    | A_Expr f 
    | A_agg _ f => S (size_funterm f)
    | A_fun _ l => S (list_size size_aggterm l)
  end.

Definition funterm_rec3 :
  forall (P : funterm -> Type),
    (forall v, P (F_Constant v)) ->
    (forall a, P (F_Dot a)) ->
    (forall f l, (forall t, List.In t l -> P t) -> P (F_Expr f l)) ->
    forall t, P t.
Proof.
intros P Hv Ha IH t.
set (n := size_funterm t).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert t Hn; induction n as [ | n].
- intros t Hn; destruct t; [apply Hv | apply Ha | ].
  apply False_rect; inversion Hn.
- intros [v | a | f l] Hn; [apply Hv | apply Ha | ].
  apply IH.
  intros t Ht; apply IHn.
  refine (le_trans _ _ _ (in_list_size size_funterm _ _ Ht) _).
  simpl in Hn; apply (le_S_n _ _ Hn).
Defined.

Definition aggterm_rec3 :
  forall (P : aggterm -> Type),
    (forall f, P (A_Expr f)) ->
    (forall ag f, P (A_agg ag f)) ->
    (forall f l, (forall t, List.In t l -> P t) -> P (A_fun f l)) ->
    forall t, P t.
Proof.
intros P Hf Ha IH t.
set (n := size_aggterm t).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert t Hn; induction n as [ | n].
- intros t Hn; destruct t; [apply Hf | apply Ha | ].
  apply False_rect; inversion Hn.
- intros [f | ag f | f l] Hn; [apply Hf | apply Ha | ].
  apply IH.
  intros t Ht; apply IHn.
  refine (le_trans _ _ _ (in_list_size size_aggterm _ _ Ht) _).
  simpl in Hn; apply (le_S_n _ _ Hn).
Defined.


Fixpoint funterm_compare (f1 f2 : funterm) : comparison :=
  match f1, f2 with
    | F_Constant c1, F_Constant c2 => Oset.compare OVal c1 c2
    | F_Constant _, _ => Lt
    | F_Dot _, F_Constant _ => Gt
    | F_Dot a1, F_Dot a2 => Oset.compare OAtt a1 a2
    | F_Dot _, F_Expr _ _ => Lt
    | F_Expr _ _, F_Constant _ => Gt
    | F_Expr _ _, F_Dot _ => Gt
    | F_Expr f1 l1, F_Expr f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA funterm_compare) (f1, l1) (f2, l2)
  end.

Lemma funterm_compare_unfold :
  forall (f1 f2 : funterm), funterm_compare f1 f2 =
  match f1, f2 with
    | F_Constant c1, F_Constant c2 => Oset.compare OVal c1 c2
    | F_Constant _, _ => Lt
    | F_Dot _, F_Constant _ => Gt
    | F_Dot a1, F_Dot a2 => Oset.compare OAtt a1 a2
    | F_Dot _, F_Expr _ _ => Lt
    | F_Expr _t1 _, F_Constant _ => Gt
    | F_Expr _ _, F_Dot _ => Gt
    | F_Expr f1 l1, F_Expr f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA funterm_compare) (f1, l1) (f2, l2)
  end.
Proof.
intros f1 f2; case f1; case f2; intros; apply refl_equal.
Qed.

Lemma funterm_compare_eq_bool_ok :
 forall t1 t2,
   match funterm_compare t1 t2 with
     | Eq => t1 = t2
     | Lt => t1 <> t2
     | Gt => t1 <> t2
   end.
Proof.
intro t1; pattern t1; apply funterm_rec3.
- intros v1 [v2 | | ]; try discriminate.
  simpl; oset_compare_tac.
- intros a1 [ | a2 | ]; try discriminate.
  simpl; oset_compare_tac.
- intros f1 l1 IH [ | | f2 l2]; try discriminate.
  assert (Aux : match compareAB (Oset.compare OSymb) 
                                (comparelA funterm_compare) (f1, l1) (f2, l2) with
                 | Eq => (f1, l1) = (f2, l2)
                 | Lt => (f1, l1) <> (f2, l2)
                 | Gt => (f1, l1) <> (f2, l2)
                 end).
  {
    apply compareAB_eq_bool_ok.
    - oset_compare_tac.
    - apply comparelA_eq_bool_ok.
      intros; apply IH; trivial.
  }
  rewrite funterm_compare_unfold.
  destruct (compareAB (Oset.compare OSymb) (comparelA funterm_compare) (f1, l1) (f2, l2)).
  + injection Aux; intros; subst; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
Qed.

Lemma funterm_compare_lt_trans :
  forall t1 t2 t3, 
    funterm_compare t1 t2 = Lt -> funterm_compare t2 t3 = Lt -> funterm_compare t1 t3 = Lt.
Proof.
intro x1; pattern x1; apply funterm_rec3.
- intros v1 x2 x3; 
    rewrite 2 (funterm_compare_unfold (F_Constant _)), (funterm_compare_unfold x2).
  destruct x2 as [v2 | a2 | f2 l2]; 
    destruct x3 as [v3 | a3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
- intros a1 x2 x3; 
    rewrite 2 (funterm_compare_unfold (F_Dot _)), (funterm_compare_unfold x2).
  destruct x2 as [v2 | a2 | f2 l2]; 
    destruct x3 as [v3 | a3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
- intros f1 l1 IH x2 x3; 
    rewrite 2 (funterm_compare_unfold (F_Expr _ _)), (funterm_compare_unfold x2).
  destruct x2 as [v2 | a2 | f2 l2]; 
    destruct x3 as [v3 | a3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
  compareAB_tac; try oset_compare_tac.
  comparelA_tac.
  + intros K1 K2; assert (J1 := funterm_compare_eq_bool_ok a1 a2); rewrite K1 in J1.
    subst a2; trivial.
  + intros K1 K2; assert (J1 := funterm_compare_eq_bool_ok a1 a2); rewrite K1 in J1.
    subst a2; trivial.
  + intros K1 K2; assert (J2 := funterm_compare_eq_bool_ok a2 a3); rewrite K2 in J2.
    subst a3; trivial.
  + apply IH; assumption.
Qed.

Lemma funterm_compare_lt_gt :
  forall t1 t2, funterm_compare t1 t2 = CompOpp (funterm_compare t2 t1).
Proof.
intro t1; pattern t1; apply funterm_rec3; clear t1.
- intros v1 [v2 | a2 | f2 l2]; simpl; [ | trivial | trivial].
  apply Oset.compare_lt_gt.
- intros a1 [v2 | a2 | f2 l2]; simpl; [trivial | | trivial].
  apply Oset.compare_lt_gt.
- intros f1 l1 IH [v2 | a2 | f2 l2]; simpl; [trivial | trivial | ].
  rewrite (Oset.compare_lt_gt OSymb f2 f1).
  case (Oset.compare OSymb f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OFun : Oset.Rcd funterm.
split with funterm_compare.
- apply funterm_compare_eq_bool_ok.
- apply funterm_compare_lt_trans.
- apply funterm_compare_lt_gt.
Defined.

Definition FFun := Fset.build OFun.

Fixpoint aggterm_compare (a1 a2 : aggterm) : comparison :=
  match a1, a2 with
    | A_Expr f1, A_Expr f2 => Oset.compare OFun f1 f2
    | A_Expr _, _ => Lt
    | A_agg _ _, A_Expr _ => Gt
    | A_agg a1 f1, A_agg a2 f2 =>
      compareAB (Oset.compare OAggregate) (Oset.compare OFun)
                (a1, f1) (a2, f2)
    | A_agg _ _, A_fun _ _ => Lt
    | A_fun _ _, A_Expr _ => Gt
    | A_fun _ _, A_agg _ _ => Gt
    | A_fun f1 l1, A_fun f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA aggterm_compare) (f1, l1) (f2, l2)
  end.

Lemma aggterm_compare_unfold :
  forall a1 a2, aggterm_compare a1 a2 =
  match a1, a2 with
    | A_Expr f1, A_Expr f2 => Oset.compare OFun f1 f2
    | A_Expr _, _ => Lt
    | A_agg _ _, A_Expr _ => Gt
    | A_agg a1 f1, A_agg a2 f2 =>
      compareAB (Oset.compare OAggregate) (Oset.compare OFun)
                (a1, f1) (a2, f2)
    | A_agg _ _, A_fun _ _ => Lt
    | A_fun _ _, A_Expr _ => Gt
    | A_fun _ _, A_agg _ _ => Gt
    | A_fun f1 l1, A_fun f2 l2 =>
      compareAB (Oset.compare OSymb) (comparelA aggterm_compare) (f1, l1) (f2, l2)
  end.
Proof.
intros a1 a2; case a1; case a2; intros; apply refl_equal.
Qed.

Lemma aggterm_compare_eq_bool_ok :
 forall t1 t2,
   match aggterm_compare t1 t2 with
     | Eq => t1 = t2
     | Lt => t1 <> t2
     | Gt => t1 <> t2
   end.
Proof.
intro t1; pattern t1; apply aggterm_rec3.
- intros f1 [ f2 | | ]; try discriminate.
  simpl; generalize (funterm_compare_eq_bool_ok f1 f2).
  case (funterm_compare f1 f2).
  + apply f_equal.
  + intros H K; apply H; injection K; exact (fun h => h).
  + intros H K; apply H; injection K; exact (fun h => h).
- intros a1 f1 [ | a2 f2 | ]; try discriminate.
  simpl; case_eq (Oset.compare OAggregate a1 a2); intro Ha.
  rewrite Oset.compare_eq_iff in Ha; subst a2.
  + generalize (funterm_compare_eq_bool_ok f1 f2);
    case (funterm_compare f1 f2).
    * apply f_equal.
    * intros H K; apply H; injection K; exact (fun h => h).
    * intros H K; apply H; injection K; exact (fun h => h).
  + intro H; injection H; intros; subst a2 f2.
    rewrite Oset.compare_eq_refl in Ha; discriminate Ha.
  + intro H; injection H; intros; subst a2 f2.
    rewrite Oset.compare_eq_refl in Ha; discriminate Ha.
- intros f1 l1 IH [ | | f2 l2]; try discriminate.
  assert (Aux : match compareAB (Oset.compare OSymb) 
                                (comparelA aggterm_compare) (f1, l1) (f2, l2) with
                 | Eq => (f1, l1) = (f2, l2)
                 | Lt => (f1, l1) <> (f2, l2)
                 | Gt => (f1, l1) <> (f2, l2)
                 end).
  {
    apply compareAB_eq_bool_ok.
    - oset_compare_tac.
    - apply comparelA_eq_bool_ok.
      intros; apply IH; trivial.
  }
  rewrite aggterm_compare_unfold.
  destruct (compareAB (Oset.compare OSymb) (comparelA aggterm_compare) (f1, l1) (f2, l2)).
  + injection Aux; intros; subst; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
Qed.

Lemma aggterm_compare_lt_trans :
  forall t1 t2 t3, 
    aggterm_compare t1 t2 = Lt -> aggterm_compare t2 t3 = Lt -> aggterm_compare t1 t3 = Lt.
Proof.
intro x1; pattern x1; apply aggterm_rec3.
- intros f1 x2 x3; 
    rewrite 2 (aggterm_compare_unfold (A_Expr _)), (aggterm_compare_unfold x2).
  destruct x2 as [f2 | a2 f2 | f2 l2]; 
    destruct x3 as [v3 | a3 f3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
- intros a1 f1 x2 x3; 
    rewrite 2 (aggterm_compare_unfold (A_agg _ _)), (aggterm_compare_unfold x2).
  destruct x2 as [f2 | a2 f2 | f2 l2]; 
    destruct x3 as [f3 | a3 f3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
  compareAB_tac; try oset_compare_tac.
- intros f1 l1 IH x2 x3; 
    rewrite 2 (aggterm_compare_unfold (A_fun _ _)), (aggterm_compare_unfold x2).
  destruct x2 as [f2 | a2 l2 | f2 l2]; 
    destruct x3 as [f3 | a3 l3 | f3 l3]; (oset_compare_tac || discriminate || trivial).
  compareAB_tac; try oset_compare_tac.
  comparelA_tac.
  + intros K1 K2; assert (J1 := aggterm_compare_eq_bool_ok a1 a2); rewrite K1 in J1.
    subst a2; trivial.
  + intros K1 K2; assert (J1 := aggterm_compare_eq_bool_ok a1 a2); rewrite K1 in J1.
    subst a2; trivial.
  + intros K1 K2; assert (J2 := aggterm_compare_eq_bool_ok a2 a3); rewrite K2 in J2.
    subst a3; trivial.
  + apply IH; assumption.
Qed.

Lemma aggterm_compare_lt_gt :
  forall t1 t2, aggterm_compare t1 t2 = CompOpp (aggterm_compare t2 t1).
Proof.
intro t1; pattern t1; apply aggterm_rec3; clear t1.
- intros f1 [f2 | a2 l2 | f2 l2]; simpl; [ | trivial | trivial].
  apply funterm_compare_lt_gt.
- intros a1 f1 [f2 | a2 l2 | f2 l2]; simpl; [trivial | | trivial].
  rewrite (Oset.compare_lt_gt OAggregate a2 a1).
  case (Oset.compare OAggregate a1 a2); simpl; trivial.
  apply funterm_compare_lt_gt.
- intros f1 l1 IH [f2 | a2 l2 | f2 l2]; simpl; [trivial | trivial | ].
  rewrite (Oset.compare_lt_gt OSymb f2 f1).
  case (Oset.compare OSymb f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OAgg : Oset.Rcd aggterm.
split with aggterm_compare.
- apply aggterm_compare_eq_bool_ok.
- apply aggterm_compare_lt_trans.
- apply aggterm_compare_lt_gt.
Defined.

Definition FAgg := Fset.build OAgg.

(* Notation default_value := (Expression.default_value E).*)

Fixpoint att_of_funterm (e : funterm) :=
  match e with
    | F_Constant _ => emptysetS
    | F_Dot a => Fset.singleton A a
    | F_Expr _ l => Fset.Union A (List.map att_of_funterm l)
  end.

Fixpoint att_of_aggterm (ag : aggterm) :=
  match ag with
    | A_Expr e 
    | A_agg _ e => att_of_funterm e
    | A_fun _ l => Fset.Union A (List.map att_of_aggterm l)
  end.

Lemma att_of_funterm_unfold :
  forall e, att_of_funterm e =
  match e with
    | F_Constant _ => emptysetS
    | F_Dot a => Fset.singleton A a
    | F_Expr _ l => Fset.Union A (List.map att_of_funterm l)
  end.
Proof.
intros e; case e; intros; apply refl_equal.
Qed.

Lemma att_of_aggterm_unfold :
  forall ag, att_of_aggterm ag =
             match ag with
               | A_Expr e 
               | A_agg _ e => att_of_funterm e
               | A_fun _ l => Fset.Union A (List.map att_of_aggterm l)
             end.
Proof.
intro ag; case ag; intros; apply refl_equal.
Qed.

Hypothesis interp_symb : symb -> list value -> value.
Hypothesis interp_aggregate : aggregate -> list value -> value.

(* Evaluation in an environment :-( *)

(*
Fixpoint interp_dot (B : Type) (env : list (Fset.set A * B * listT)) (a : attribute T) :=
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l1) :: env => 
      match quicksort (OTuple T) l1 with
        | nil => interp_dot env a
        | t1 :: _ => if a inS? support T t1 
                     then dot T t1 a
                     else interp_dot env a
      end
  end.
   
Lemma interp_dot_unfold :
  forall (B : Type) env a, interp_dot (B := B) env a =
  match env with
    | nil => default_value T (type_of_attribute T a)
    | (_, _, l1) :: env => 
      match quicksort (OTuple T) l1 with
        | nil => interp_dot env a
        | t1 :: _ => if a inS? support T t1 
                     then dot T t1 a
                     else interp_dot env a
      end
  end.
Proof.
intros B env a; destruct env; intros; trivial.
Qed.

Definition groups_of_env_slice (s : (setA * group_by * (list (tuple T)))) :=
  match s with
    | (_, Group_By g, _) => g
    | (sa, Group_Fine, _) => List.map (fun a => F_Dot _ _ a) ({{{sa}}})
  end.

*)
Hypothesis SEnv : Type.
Notation Env := (list SEnv).

Hypothesis interp_dot_env_slice : SEnv -> attribute -> option value. 
Hypothesis attributes_of_env_slice : SEnv -> Fset.set A.
Hypothesis groups_of_env_slice : SEnv -> (* list aggterm *) list funterm.
Hypothesis unfold_env_slice : SEnv -> list SEnv.
Hypothesis default_value : attribute -> value.

Fixpoint interp_dot env (a : attribute) :=
  match env with
    | nil => default_value a
    | slc :: env => match interp_dot_env_slice slc a with
                      | Some v => v
                      | None => interp_dot env a
                    end
  end.
      
Lemma interp_dot_unfold :
  forall env a, interp_dot env a =
  match env with
    | nil => default_value a
    | slc :: env => match interp_dot_env_slice slc a with
                      | Some v => v
                      | None => interp_dot env a
                    end
  end.
Proof.
intros env a; case env; intros; apply refl_equal.
Qed.

Fixpoint interp_funterm env t := 
  match t with
    | F_Constant c => c
    | F_Dot a => interp_dot env a
    | F_Expr f l => interp_symb f (List.map (fun x => interp_funterm env x) l)
  end.

Lemma interp_funterm_unfold :
  forall env t, interp_funterm env t =
  match t with
    | F_Constant c => c
    | F_Dot a => interp_dot env a
    | F_Expr f l => interp_symb f (List.map (fun x => interp_funterm env x) l)
  end.
Proof.
intros env t; case t; intros; apply refl_equal.
Qed.

Fixpoint is_built_upon g f :=
  match f with
    | F_Constant _ => true
    | F_Dot _ => Oset.mem_bool OFun f g
    | F_Expr s l => Oset.mem_bool OFun f g || forallb (is_built_upon g) l
  end.

(* Fixpoint built_upon_agg g a :=
  match a with
    | A_Expr _ => Oset.mem_bool OAgg a g
    | A_agg ag f => Oset.mem_bool OAgg a g
    | A_fun s l => Oset.mem_bool OAgg a g || forallb (built_upon_agg g) l
  end.
*)

Definition is_a_suitable_env (sa : Fset.set A) env f :=
  is_built_upon  (map (fun a => F_Dot a) ({{{sa}}}) ++ flat_map groups_of_env_slice env) f.

Fixpoint find_eval_env (env : Env) f := 
  match env with
    | nil => if is_built_upon nil f 
             then Some nil
             else None
    | slc1 :: env' => 
      match find_eval_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_suitable_env (attributes_of_env_slice slc1) env' f
          then Some env
          else None
      end
  end.
  
Lemma find_eval_env_unfold :
  forall env f, find_eval_env env f =
  match env with
    | nil => if is_built_upon nil f 
             then Some nil
             else None
    | slc1 :: env' => 
      match find_eval_env env' f with
        | Some _ as e => e
        | None =>
          if is_a_suitable_env (attributes_of_env_slice slc1) env' f
          then Some env
          else None
      end
  end.
Proof.
intros env f; case env; intros; apply refl_equal.
Qed.

Fixpoint interp_aggterm (env : Env) (ag : aggterm) := 
  match ag with
  | A_Expr ft => interp_funterm env ft
  | A_agg ag ft => 
    let env' := 
        if Fset.is_empty A (att_of_funterm ft)
        then Some env 
        else find_eval_env env ft in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun f lag => interp_symb f (List.map (fun x => interp_aggterm env x) lag)
  end.

Lemma interp_aggterm_unfold :
  forall env ag, interp_aggterm env ag =
  match ag with
  | A_Expr ft => interp_funterm env ft
  | A_agg ag ft => 
    let env' := 
        if Fset.is_empty A (att_of_funterm ft)
        then Some env 
        else find_eval_env env ft in
    let lenv := 
        match env' with 
          | None | Some nil => nil
          | Some (slc1 :: env'') => map (fun slc => slc :: env'') (unfold_env_slice slc1)
        end in
        interp_aggregate ag (List.map (fun e => interp_funterm e ft) lenv)
  | A_fun f lag => interp_symb f (List.map (fun x => interp_aggterm env x) lag)
  end.
Proof.
intros env ag; case ag; intros; apply refl_equal.
Qed.

Hypothesis equiv_env_slice : SEnv -> SEnv -> Prop.

Hypothesis equiv_env_slice_refl : forall slc, equiv_env_slice slc slc.

Hypothesis equiv_env_slice_sym : 
  forall slc1 slc2, equiv_env_slice slc1 slc2 <-> equiv_env_slice slc2 slc1.

Hypothesis attributes_of_env_slice_eq :
  forall slc1 slc2, 
    equiv_env_slice slc1 slc2 -> attributes_of_env_slice slc1 =S= attributes_of_env_slice slc2.

Hypothesis unfold_env_slice_eq : 
  forall slc1 slc2, equiv_env_slice slc1 slc2 -> 
                    Forall2 equiv_env_slice (unfold_env_slice slc1) (unfold_env_slice slc2).

Hypothesis groups_of_env_slice_eq :
  forall slc1 slc2, equiv_env_slice slc1 slc2 -> 
                    forall f, In f (groups_of_env_slice slc1) <-> In f (groups_of_env_slice slc2).

Hypothesis interp_dot_env_slice_eq :
  forall a e1 e2, equiv_env_slice e1 e2 -> interp_dot_env_slice e1 a = interp_dot_env_slice e2 a.

Definition equiv_env e1 e2 := Forall2 equiv_env_slice e1 e2.

Lemma equiv_env_refl : forall e, equiv_env e e.
Proof.
intro e; unfold equiv_env; induction e as [ | slc1 e]; simpl; trivial.
constructor 2; [apply equiv_env_slice_refl | apply IHe].
Qed.

Lemma equiv_env_sym :
  forall e1 e2, equiv_env e1 e2 <-> equiv_env e2 e1.
Proof.
assert (H : forall e1 e2, equiv_env e1 e2 -> equiv_env e2 e1).
{
  intro e1; induction e1 as [ | s1 e1]; intros [ | s2 e2].
  - exact (fun h => h).
  - intro H; inversion H.
  - intro H; inversion H.
  - intro H; simpl in H.
    inversion H; subst.
    constructor 2.
    + rewrite equiv_env_slice_sym; assumption.
    + apply IHe1; assumption.
}
intros e1 e2; split; apply H.
Qed.

Lemma interp_dot_eq :
  forall a e1 e2, equiv_env e1 e2 -> interp_dot e1 a = interp_dot e2 a.
Proof.
Proof.
intros a e1; induction e1 as [ | slc1 e1]; intros [ | slc2 e2] H.
- apply refl_equal.
- inversion H.
- inversion H.
- simpl in H; inversion H; subst.
  simpl; rewrite <- (interp_dot_env_slice_eq _ H3).
  case (interp_dot_env_slice slc1 a); [intro; apply refl_equal | ].
  apply IHe1; assumption.
Qed.

Lemma interp_funterm_eq :
  forall f e1 e2, equiv_env e1 e2 -> interp_funterm e1 f = interp_funterm e2 f.
Proof.
intro f.
set (n := size_funterm f).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert f Hn.
induction n as [ | n];
  intros f Hn e1 e2 He. 
- destruct f; inversion Hn.
- destruct f as [c | a | f l].
  + apply refl_equal.
  + simpl; apply interp_dot_eq; trivial.
  + simpl; apply f_equal.
    rewrite <- map_eq.
    intros a Ha.
    apply IHn; [ | assumption].
    simpl in Hn.
    refine (Le.le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; apply Ha.
Qed.

Lemma is_built_upon_incl :
  forall f g1 g2, (forall x, In x g1 -> In x g2) -> 
                  is_built_upon g1 f = true -> is_built_upon g2 f = true.
Proof.
intro f; set (m := size_funterm f); assert (Hm := le_n m); unfold m at 1 in Hm.
clearbody m; revert f Hm; induction m as [ | m].
- intros e Hm; destruct e; inversion Hm.
- intros e Hm g1 g2 Hg Hf; destruct e as [c | b | f1 l]; simpl; trivial.
  + rewrite Oset.mem_bool_true_iff; apply Hg.
    simpl in Hf; rewrite Oset.mem_bool_true_iff in Hf; trivial.
  + simpl in Hf; rewrite Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
    * rewrite Bool.orb_true_iff; left.
      rewrite Oset.mem_bool_true_iff; apply Hg.
      rewrite Oset.mem_bool_true_iff in Hf; trivial.
    * rewrite Bool.orb_true_iff; right.
      rewrite forallb_forall; intros x Hx.
      {
        apply IHm with g1; trivial.
        - simpl in Hm; refine (le_trans _ _ _ _ (le_S_n _ _ Hm)).
          apply in_list_size; trivial.
        - rewrite forallb_forall in Hf; apply Hf; trivial.
      }
Qed.

Lemma is_a_suitable_env_eq :
  forall e sa1 env1 sa2 env2, sa1 =S= sa2 -> equiv_env env1 env2 ->
                              is_a_suitable_env sa1 env1 e = is_a_suitable_env sa2 env2 e.
Proof.
assert (H : forall env1 env2 slc1, 
              equiv_env env1 env2 -> In slc1 env1 -> 
              exists slc2, In slc2 env2 /\ equiv_env_slice slc1 slc2).
{
  intro env1; induction env1 as [ | s1 e1]; intros [ | s2 e2] slc1 He Hs.
  - contradiction Hs.
  - inversion He.
  - inversion He.
  - simpl in He; inversion He; subst.
    simpl in Hs; destruct Hs as [Hs | Hs].
    + subst slc1; exists s2; split; [left | ]; trivial.
    + destruct (IHe1 _ _ H4 Hs) as [slc2 [K1 K2]].
      exists slc2; split; [right | ]; trivial.
}
intros e sa1 env1 sa2 env2 Hsa Henv.
unfold is_a_suitable_env; rewrite eq_bool_iff; split; 
apply is_built_upon_incl; intros f Hf;
(destruct (in_app_or _ _ _ Hf) as [Kf | Kf]; apply in_or_app; [left | right]).
- rewrite <- (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [slc1 [H1 H2]].
  destruct (H _ _ _ Henv H1) as [slc2 [H3 H4]].
  rewrite in_flat_map; exists slc2; split; [assumption | ].
  rewrite <- (groups_of_env_slice_eq H4); assumption.
- rewrite (Fset.elements_spec1 _ _ _ Hsa); assumption.
- rewrite in_flat_map in Kf; destruct Kf as [slc1 [H1 H2]].
  rewrite equiv_env_sym in Henv.
  destruct (H _ _ _ Henv H1) as [slc2 [H3 H4]].
  rewrite in_flat_map; exists slc2; split; [assumption | ].
  rewrite <- (groups_of_env_slice_eq H4); assumption.
Qed.

Lemma find_eval_env_eq :
  forall e env1 env2, 
    equiv_env env1 env2 -> 
    match (find_eval_env env1 e), (find_eval_env env2 e) with
      | None, None => True
      | Some e1, Some e2 => equiv_env e1 e2
      | _, _ => False
    end.
Proof.
intros e env1; induction env1 as [ | slc1 env1]; intros [ | slc2 env2] He.
- simpl; case (is_built_upon nil e); trivial.
- inversion He.
- inversion He.
- inversion He; subst.
  assert (IH := IHenv1 _ H4).
  simpl.
  destruct (find_eval_env env1 e) as [l1 | ];
    destruct (find_eval_env env2 e) as [l2 | ]; try contradiction IH.
  + assumption.
  + assert (H1 := attributes_of_env_slice_eq H2).
    rewrite <- (is_a_suitable_env_eq e _ _ H1 H4).
    case (is_a_suitable_env (attributes_of_env_slice slc1) env1 e).
    * constructor 2; trivial.
    * trivial.
Qed.
    
Lemma interp_aggterm_eq :
  forall e env1 env2, equiv_env env1 env2 -> interp_aggterm env1 e = interp_aggterm env2 e.
Proof.
intro a.
set (n := size_aggterm a).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert a Hn.
induction n as [ | n]; intros a Hn env1 env2 He.
- destruct a; inversion Hn.
- destruct a as [f | a f | f l]; simpl.
  + apply interp_funterm_eq; trivial.
  + apply f_equal.
    case (Fset.is_empty A (att_of_funterm f)).
    * destruct env1 as [ | slc1 e1]; destruct env2 as [ | slc2 e2];
      try inversion He; [apply refl_equal | ].
      subst.
      rewrite 2 map_map.
      assert (H' := unfold_env_slice_eq H2).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      {
        revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'.
        - apply refl_equal.
        - inversion H'.
        - inversion H'.
        - inversion H' as [ | _t1 _t2 _l1 _l2 Ht Hl K3 K4]; subst.
          simpl map; apply f_equal2.
          + apply interp_funterm_eq; constructor 2; trivial.
          + apply IHl1; trivial.
      }
    * assert (H := find_eval_env_eq f He).
      destruct (find_eval_env env1 f) as [[ | slc1 e1] | ];
        destruct (find_eval_env env2 f) as [[ | slc2 e2] | ];
        try inversion H; trivial.
      subst; rewrite 2 map_map.
      simpl in H.
      assert (H' := unfold_env_slice_eq H3).
      set (l1 := unfold_env_slice slc1) in *; clearbody l1.
      set (l2 := unfold_env_slice slc2) in *; clearbody l2.
      revert l2 H'; induction l1 as [ | t1 l1]; intros [ | t2 l2] H'; 
      try (inversion H'; fail); trivial.
      {
        inversion H'; subst.
        simpl map; apply f_equal2.
        - apply interp_funterm_eq; constructor 2; trivial.
        - apply IHl1; trivial.
      }
  + apply f_equal; rewrite <- map_eq.
    intros a Ha; apply IHn; trivial.
    simpl in Hn.
    refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
Qed.

End Sec.

