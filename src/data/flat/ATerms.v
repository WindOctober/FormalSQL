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

Require Import List Bool Arith NArith.
Require Import BasicTacs BasicFacts Bool3 ListFacts ListSort ListPermut
        OrderedSet Partition FiniteSet FiniteBag FiniteCollection Join
        FTuples FTerms.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Inductive aggterm : Type := 
| A_Expr : funterm T -> aggterm
| A_agg : aggregate T -> funterm T -> aggterm
| A_fun : symbol T -> list aggterm -> aggterm.


Fixpoint size_aggterm (t : aggterm) : nat :=
  match t with
    | A_Expr f 
    | A_agg _ f => S (size_funterm T f)
    | A_fun _ l => S (list_size size_aggterm l)
  end.

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


Fixpoint aggterm_compare (a1 a2 : aggterm) : comparison :=
  match a1, a2 with
    | A_Expr f1, A_Expr f2 => Oset.compare (OFun T) f1 f2
    | A_Expr _, _ => Lt
    | A_agg _ _, A_Expr _ => Gt
    | A_agg a1 f1, A_agg a2 f2 =>
      compareAB (Oset.compare (OAgg T)) (Oset.compare (OFun T))
                (a1, f1) (a2, f2)
    | A_agg _ _, A_fun _ _ => Lt
    | A_fun _ _, A_Expr _ => Gt
    | A_fun _ _, A_agg _ _ => Gt
    | A_fun f1 l1, A_fun f2 l2 =>
      compareAB (Oset.compare (OSymb T)) (comparelA aggterm_compare) (f1, l1) (f2, l2)
  end.

Lemma aggterm_compare_unfold :
  forall a1 a2, aggterm_compare a1 a2 =
  match a1, a2 with
    | A_Expr f1, A_Expr f2 => Oset.compare (OFun T) f1 f2
    | A_Expr _, _ => Lt
    | A_agg _ _, A_Expr _ => Gt
    | A_agg a1 f1, A_agg a2 f2 =>
      compareAB (Oset.compare (OAgg T)) (Oset.compare (OFun T))
                (a1, f1) (a2, f2)
    | A_agg _ _, A_fun _ _ => Lt
    | A_fun _ _, A_Expr _ => Gt
    | A_fun _ _, A_agg _ _ => Gt
    | A_fun f1 l1, A_fun f2 l2 =>
      compareAB (Oset.compare (OSymb T)) (comparelA aggterm_compare) (f1, l1) (f2, l2)
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
  simpl; generalize (funterm_compare_eq_bool_ok T f1 f2).
  case (funterm_compare T f1 f2).
  + apply f_equal.
  + intros H K; apply H; injection K; exact (fun h => h).
  + intros H K; apply H; injection K; exact (fun h => h).
- intros a1 f1 [ | a2 f2 | ]; try discriminate.
  simpl; case_eq (Oset.compare (OAgg T) a1 a2); intro Ha.
  rewrite Oset.compare_eq_iff in Ha; subst a2.
  + generalize (funterm_compare_eq_bool_ok T f1 f2);
    case (funterm_compare T f1 f2).
    * apply f_equal.
    * intros H K; apply H; injection K; exact (fun h => h).
    * intros H K; apply H; injection K; exact (fun h => h).
  + intro H; injection H; intros; subst a2 f2.
    rewrite Oset.compare_eq_refl in Ha; discriminate Ha.
  + intro H; injection H; intros; subst a2 f2.
    rewrite Oset.compare_eq_refl in Ha; discriminate Ha.
- intros f1 l1 IH [ | | f2 l2]; try discriminate.
  assert (Aux : match compareAB (Oset.compare (OSymb T)) 
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
  destruct (compareAB (Oset.compare (OSymb T)) (comparelA aggterm_compare) (f1, l1) (f2, l2)).
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
  rewrite (Oset.compare_lt_gt (OAgg T) a2 a1).
  case (Oset.compare (OAgg T) a1 a2); simpl; trivial.
  apply funterm_compare_lt_gt.
- intros f1 l1 IH [f2 | a2 l2 | f2 l2]; simpl; [trivial | trivial | ].
  rewrite (Oset.compare_lt_gt (OSymb T) f2 f1).
  case (Oset.compare (OSymb T) f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OAggT : Oset.Rcd aggterm.
split with aggterm_compare.
- apply aggterm_compare_eq_bool_ok.
- apply aggterm_compare_lt_trans.
- apply aggterm_compare_lt_gt.
Defined.

Fixpoint variables_ag (a : aggterm) :=
  match a with
  | A_Expr f => variables_ft T f
  | A_agg _ f => variables_ft T f
  | A_fun _ l =>  Fset.Union (A T) (map variables_ag l)
  end.
    
Fixpoint extract_funterms (g : list aggterm) :=
  match g with
  | nil => nil
  | A_Expr ft :: g => ft :: extract_funterms g
  | _ :: g => extract_funterms g
  end.

Lemma in_extract_funterms :
  forall x g, In x (extract_funterms g) <-> In (A_Expr x) g.
Proof.
intros x g; induction g as [ | g1 g]; simpl; [split; exact (fun h => h) | ].
destruct g1; split; intro H.
- simpl in H; destruct H as [H | H].
  + left; apply f_equal; assumption.
  + right; rewrite <- IHg; assumption.
- destruct H as [H | H]; [injection H; intro; subst; left; apply refl_equal | ].
  right; rewrite IHg; assumption.
- right; rewrite <- IHg; assumption.
- destruct H as [H | H]; [discriminate H | ].
  rewrite IHg; assumption.
- right; rewrite <- IHg; assumption.
- destruct H as [H | H]; [discriminate H | ].
  rewrite IHg; assumption.
Qed.

Lemma extract_funterms_app :
  forall g1 g2, extract_funterms (g1 ++ g2) = extract_funterms g1 ++ extract_funterms g2.
Proof.
intro g1; induction g1 as [ | [f1 | a1 f1 | f1 la1] g1]; intros g2; simpl; trivial.
apply f_equal; apply IHg1.
Qed.

Lemma extract_funterms_A_Expr :
  forall l, extract_funterms (map (fun x => A_Expr (F_Dot T x)) l) = map (fun x => F_Dot T x) l.
Proof.
intro l; induction l as [ | a1 l]; [apply refl_equal | ].
simpl; apply f_equal; apply IHl.
Qed.

Lemma extract_funterms_incl :
  forall g1 g2, (forall x, In x g1 -> In x g2) -> 
                forall x, In x (extract_funterms g1) -> In x (extract_funterms g2).
Proof.
intro g1; induction g1 as [ | [f1 | | ] g1]; 
  intros g2 Hg; intros x Hx; [contradiction Hx | | | ].
- simpl in Hx; destruct Hx as [Hx | Hx]; 
    [ | apply IHg1; [do 2 intro; apply Hg; right| ]; assumption].
  subst x.
  destruct (in_split _ _ (Hg _ (or_introl _ (refl_equal _)))) as [l1 [l2 H]]; subst g2.
  rewrite extract_funterms_app; simpl.
  apply in_or_app; right; left; apply refl_equal.
- apply IHg1; [do 2 intro; apply Hg; right; assumption | apply Hx]. 
- apply IHg1; [do 2 intro; apply Hg; right; assumption | apply Hx]. 
Qed.

Fixpoint is_built_upon_ag g a1 :=
  match a1 with
  | A_Expr ft => is_built_upon_ft _ (extract_funterms g) ft
  | A_agg a f => Oset.mem_bool OAggT a1 g || is_built_upon_ft _ (extract_funterms g) f
  | A_fun f la => Oset.mem_bool OAggT a1 g || forallb (is_built_upon_ag g) la
  end.

Lemma in_is_built_upon_ag :
  forall g f, In f g -> is_built_upon_ag g f = true.
Proof.
intros g f H; destruct f; simpl.
- rewrite <- in_extract_funterms in H; apply in_is_built_upon_ft; assumption.
- rewrite Bool.Bool.orb_true_iff; left; rewrite Oset.mem_bool_true_iff; assumption.
- rewrite Bool.Bool.orb_true_iff; left; rewrite Oset.mem_bool_true_iff; assumption.
Qed.

Lemma is_built_upon_ag_trans :
  forall f g1 g2, (forall x, In x g1 -> is_built_upon_ag g2 x = true) ->
                  is_built_upon_ag g1 f = true -> is_built_upon_ag g2 f = true.
Proof.
intro f; set (m := size_aggterm f); assert (Hm := le_n m); unfold m at 1 in Hm.
clearbody m; revert f Hm; induction m as [ | m].
- intros e Hm; destruct e; inversion Hm.
- intros e Hm g1 g2 Hg Hf; destruct e as [f | ag f | f1 la].
  + simpl in Hf; simpl; revert Hf; apply is_built_upon_ft_trans.
    intros x Hx; rewrite in_extract_funterms in Hx.
    apply (Hg _ Hx).
  + simpl in Hf.
    case_eq (Oset.mem_bool OAggT (A_agg ag f) g1); intro Kf.
    * rewrite Oset.mem_bool_true_iff in Kf.
      apply Hg; assumption.
    * rewrite Kf, Bool.Bool.orb_false_l in Hf; simpl; rewrite Bool.Bool.orb_true_iff; right.
      revert Hf; apply is_built_upon_ft_trans; intros x Hx.
      rewrite in_extract_funterms in Hx.
      apply (Hg _ Hx).
  + simpl in Hf.
    case_eq (Oset.mem_bool OAggT (A_fun f1 la) g1); intro Kf.
    * rewrite Oset.mem_bool_true_iff in Kf.
      apply Hg; assumption.
    * rewrite Kf, Bool.Bool.orb_false_l, forallb_forall in Hf.
      simpl; rewrite Bool.Bool.orb_true_iff; right; rewrite forallb_forall.
      intros x Hx; generalize (Hf _ Hx); apply IHm; [ | trivial].
      simpl in Hm; refine (le_trans _ _ _ _ (le_S_n _ _ Hm)).
      apply in_list_size; assumption.
Qed.

Lemma is_built_upon_ag_incl :
  forall f g1 g2, (forall x, In x g1 -> In x g2) -> 
                  is_built_upon_ag g1 f = true -> is_built_upon_ag g2 f = true.
Proof.
intros f g1 g2 H; apply is_built_upon_ag_trans.
intros x Hx; apply in_is_built_upon_ag; apply H; assumption.
Qed.

Lemma is_built_upon_ag_permut :
  forall g1 g2 f, Oset.permut OAggT g1 g2 -> is_built_upon_ag g1 f = is_built_upon_ag g2 f.
Proof.
intros g1 g2 f; set (n := size_aggterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn H; [destruct f; inversion Hn | ].
destruct f as [f | a f | f l]; simpl.
- apply is_built_upon_ft_permut.
  clear n f IHn Hn.
  revert g2 H; induction g1 as [ | t1 g1]; 
    intros g2 H; [inversion H; subst; apply Oset.permut_refl | ].
  inversion H; subst; simpl.
  rewrite Oset.compare_eq_iff in H2; subst b; rewrite extract_funterms_app; simpl.
  destruct t1 as [f1 | a1 f1 | f1 la1].
  + apply Pcons; 
      [apply Oset.compare_eq_refl 
      | rewrite <- extract_funterms_app; apply IHg1; assumption].
  + rewrite <- extract_funterms_app; apply IHg1; assumption.
  + rewrite <- extract_funterms_app; apply IHg1; assumption.
- apply f_equal2.
  + apply Oset.permut_mem_bool_eq; assumption.
  + apply is_built_upon_ft_permut.
    clear n f IHn Hn.
    revert g2 H; induction g1 as [ | t1 g1]; 
    intros g2 H; [inversion H; subst; apply Oset.permut_refl | ].
    inversion H; subst; simpl.
    rewrite Oset.compare_eq_iff in H2; subst b; rewrite extract_funterms_app; simpl.
    destruct t1 as [f1 | a1 f1 | f1 la1].
    * apply Pcons; 
        [apply Oset.compare_eq_refl 
        | rewrite <- extract_funterms_app; apply IHg1; assumption].
    * rewrite <- extract_funterms_app; apply IHg1; assumption.
    * rewrite <- extract_funterms_app; apply IHg1; assumption.
- apply f_equal2.
   + apply Oset.permut_mem_bool_eq; assumption.
   + apply forallb_eq.
     intros t Ht; apply IHn; [ | assumption].
     simpl in Hn.
     refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
     apply in_list_size; assumption.
Qed.

Lemma is_built_upon_ag_restrict :
  forall g s1 s2 f,
    (forall e : attribute T, e inS (s2 interS variables_ag f) -> e inS s1) ->
    is_built_upon_ag
      (map (fun a0 : attribute T => A_Expr (F_Dot T a0)) ({{{s1 unionS s2}}}) ++ g) f =
    is_built_upon_ag
      (map (fun a0 : attribute T => A_Expr (F_Dot T a0)) ({{{s1}}}) ++ g) f.
Proof.
intros g s1 s2 f.
set (n := size_aggterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn Hf; [destruct f; inversion Hn | ].
assert (Aux : forall l,
           extract_funterms (map (fun a0 => A_Expr (F_Dot T a0)) l) =
           map (fun a0 : attribute T => F_Dot T a0) l).
{
  induction l as [ | a1 l]; [apply refl_equal | ].
  simpl; apply f_equal; apply IHl.
}
assert (Aux2 : forall a f l, 
             Oset.mem_bool OAggT (A_agg a f) (map (fun a0 => A_Expr (F_Dot T a0)) l) = false).
{
  intros a _f l; induction l as [ | a1 l]; [apply refl_equal | simpl; apply IHl].
}
assert (Aux3 : forall f k l, 
             Oset.mem_bool OAggT (A_fun f k) (map (fun a0 => A_Expr (F_Dot T a0)) l) = false).
{
  intros _f k l; induction l as [ | a1 l]; [apply refl_equal | simpl; apply IHl].
}
destruct f as [c | a | fc lf]; simpl.
- rewrite !extract_funterms_app.
  refine (trans_eq _ (trans_eq (is_built_upon_ft_eq _ _ _ _ _ Hf) _)); 
    rewrite Aux; apply refl_equal.
- rewrite !Oset.mem_bool_app, !extract_funterms_app, !Aux.
  apply f_equal2; [ | apply is_built_upon_ft_eq; assumption].
  rewrite !Aux2; apply refl_equal.
- apply f_equal2.
  + rewrite !Oset.mem_bool_app, !Aux3; apply refl_equal.
  + apply forallb_eq.
    intros f Kf; apply IHn.
    * simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); apply in_list_size; assumption.
    * intros a Ha; apply Hf.
      rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ha.
      rewrite Fset.mem_inter, (proj1 Ha), Bool.Bool.andb_true_l; simpl.
      rewrite Fset.mem_Union.
      eexists; split; [ | apply (proj2 Ha)].
      rewrite in_map_iff; eexists; split; [ | apply Kf]; trivial.
Qed.

End Sec.


