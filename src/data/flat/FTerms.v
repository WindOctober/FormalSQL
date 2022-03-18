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
        FTuples.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.


Inductive funterm : Type :=
| F_Constant : value T -> funterm
| F_Dot : attribute T -> funterm
| F_Expr : symbol T -> list funterm -> funterm.

Fixpoint size_funterm (t : funterm) : nat :=
  match t with
    | F_Constant _
    | F_Dot _ => 1%nat
    | F_Expr _ l => S (list_size size_funterm l)
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

Fixpoint funterm_compare (f1 f2 : funterm) : comparison :=
  match f1, f2 with
    | F_Constant c1, F_Constant c2 => Oset.compare (OVal T) c1 c2
    | F_Constant _, _ => Lt
    | F_Dot _, F_Constant _ => Gt
    | F_Dot a1, F_Dot a2 => Oset.compare (OAtt T) a1 a2
    | F_Dot _, F_Expr _ _ => Lt
    | F_Expr _ _, F_Constant _ => Gt
    | F_Expr _ _, F_Dot _ => Gt
    | F_Expr f1 l1, F_Expr f2 l2 =>
      compareAB (Oset.compare (OSymb T)) (comparelA funterm_compare) (f1, l1) (f2, l2)
  end.

Lemma funterm_compare_unfold :
  forall (f1 f2 : funterm), funterm_compare f1 f2 =
  match f1, f2 with
    | F_Constant c1, F_Constant c2 => Oset.compare (OVal T) c1 c2
    | F_Constant _, _ => Lt
    | F_Dot _, F_Constant _ => Gt
    | F_Dot a1, F_Dot a2 => Oset.compare (OAtt T) a1 a2
    | F_Dot _, F_Expr _ _ => Lt
    | F_Expr _t1 _, F_Constant _ => Gt
    | F_Expr _ _, F_Dot _ => Gt
    | F_Expr f1 l1, F_Expr f2 l2 =>
      compareAB (Oset.compare (OSymb T)) (comparelA funterm_compare) (f1, l1) (f2, l2)
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
  assert (Aux : match compareAB (Oset.compare (OSymb T)) 
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
  destruct (compareAB (Oset.compare (OSymb T)) (comparelA funterm_compare) (f1, l1) (f2, l2)).
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
  rewrite (Oset.compare_lt_gt (OSymb T) f2 f1).
  case (Oset.compare (OSymb T) f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OFun : Oset.Rcd funterm.
split with funterm_compare.
- apply funterm_compare_eq_bool_ok.
- apply funterm_compare_lt_trans.
- apply funterm_compare_lt_gt.
Defined.

Fixpoint variables_ft (f : funterm) :=
  match f with
  | F_Constant _ => Fset.empty (A T)
  | F_Dot a => Fset.singleton (A T) a
  | F_Expr _ l => Fset.Union (A T) (map variables_ft l)
  end.

Fixpoint is_built_upon_ft g f :=
  match f with
    | F_Constant _ => true
    | F_Dot _ => Oset.mem_bool OFun f g
    | F_Expr s l => Oset.mem_bool OFun f g || forallb (is_built_upon_ft g) l
  end.

Lemma is_built_upon_ft_unfold :
  forall g f, is_built_upon_ft g f =
  match f with
    | F_Constant _ => true
    | F_Dot _ => Oset.mem_bool OFun f g
    | F_Expr s l => Oset.mem_bool OFun f g || forallb (is_built_upon_ft g) l
  end.
Proof.
intros g f; case f; intros; apply refl_equal.
Qed.

Lemma empty_vars_is_built_upon_ft :
  forall f, Fset.is_empty _ (variables_ft f) = true ->
            forall g, is_built_upon_ft g f = true.
Proof.
intro f; set (n := size_funterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn Hf g; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; simpl; [apply refl_equal | | ].
- simpl in Hf; rewrite Fset.is_empty_spec, Fset.equal_spec in Hf.
  assert (Abs := Hf a); rewrite Fset.singleton_spec, Oset.eq_bool_refl, Fset.empty_spec in Abs.
  discriminate Abs.
- rewrite Bool.Bool.orb_true_iff; right; rewrite forallb_forall; intros x Hx.
  apply IHn.
  + simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
    apply in_list_size; assumption.
  + rewrite Fset.is_empty_spec, Fset.equal_spec; intro a.
    rewrite Fset.is_empty_spec, Fset.equal_spec in Hf.
    rewrite Fset.empty_spec.
    case_eq (a inS? variables_ft x); intro Ha; [ | apply refl_equal].
    assert (Abs := Hf a); rewrite Fset.empty_spec in Abs; simpl in Abs.
    rewrite <- not_true_iff_false in Abs; apply False_rec; apply Abs.
    rewrite Fset.mem_Union; eexists; split; [ | apply Ha].
    rewrite in_map_iff; eexists; split; [ | apply Hx]; apply refl_equal.
Qed.

Lemma in_is_built_upon_ft :
  forall g f, In f g -> is_built_upon_ft g f = true.
Proof.
intros g f H; destruct f; simpl; trivial.
- rewrite Oset.mem_bool_true_iff; assumption.
- rewrite Bool.Bool.orb_true_iff; left; rewrite Oset.mem_bool_true_iff; assumption.
Qed.

Lemma is_built_upon_ft_eq :
  forall g s1 s2 f,
    (forall e : attribute T, e inS (s2 interS variables_ft f) -> e inS s1) ->
    is_built_upon_ft
      (map (fun a0 : attribute T => F_Dot a0) ({{{s1 unionS s2}}}) ++ g) f =
    is_built_upon_ft (map (fun a0 : attribute T => F_Dot a0) ({{{s1}}}) ++ g) f.
Proof.
intros g s1 s2 f.
set (n := size_funterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn Hf; [destruct f; inversion Hn | ].
destruct f as [c | a | fc lf]; [apply refl_equal | | ]; simpl.
- rewrite !Oset.mem_bool_app; apply f_equal2; [ | apply refl_equal].
  assert (Hfa : a inS s2 -> a inS s1).
  {
    intros Ha; apply Hf.
    rewrite Fset.mem_inter, Ha, Bool.Bool.andb_true_l; simpl.
    rewrite Fset.singleton_spec, Oset.eq_bool_refl.
    apply refl_equal.
  }
  apply eq_bool_iff; split; intro H; 
    rewrite Oset.mem_bool_true_iff, in_map_iff in H; destruct H as [_a [Ha _H]];
      injection Ha; clear Ha; intro Ha; subst _a.
  + rewrite Oset.mem_bool_true_iff, in_map_iff.
    exists a; split; [apply refl_equal | ].
    apply Fset.mem_in_elements.
    assert (H := Fset.in_elements_mem _ _ _ _H); rewrite Fset.mem_union in H.
    case_eq (a inS? s1); intro Ha1; [apply refl_equal | ].
    rewrite Ha1, Bool.Bool.orb_false_l in H.
    rewrite <- Ha1; apply Hfa; apply H.
  + rewrite Oset.mem_bool_true_iff, in_map_iff.
    exists a; split; [apply refl_equal | ].
    apply Fset.mem_in_elements; rewrite Fset.mem_union.
    rewrite (Fset.in_elements_mem _ _ _ _H); apply refl_equal.
- apply f_equal2.
  + rewrite !Oset.mem_bool_app; apply f_equal2; [ | apply refl_equal].
    rewrite eq_bool_iff; split; intro H;
    rewrite Oset.mem_bool_true_iff, in_map_iff in H; destruct H as [_a [Ha _H]];
      discriminate Ha.
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

Lemma is_built_upon_ft_permut :
  forall g1 g2 f, Oset.permut OFun g1 g2 -> is_built_upon_ft g1 f = is_built_upon_ft g2 f.
Proof.
intros g1 g2 f; set (n := size_funterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn H; [destruct f; inversion Hn | ].
destruct f as [c | a | f l]; [apply refl_equal | | ]; simpl.
- apply Oset.permut_mem_bool_eq; assumption.
-  apply f_equal2.
   + apply Oset.permut_mem_bool_eq; assumption.
   + apply forallb_eq.
     intros t Ht; apply IHn; [ | assumption].
     simpl in Hn.
     refine (le_trans _ _ _ _ (le_S_n _ _ Hn)).
     apply in_list_size; assumption.
Qed.

Lemma is_built_upon_ft_trans :
  forall f g1 g2, (forall x, In x g1 -> is_built_upon_ft g2 x = true) ->
                  is_built_upon_ft g1 f = true -> is_built_upon_ft g2 f = true.
Proof.
intro f; set (m := size_funterm f); assert (Hm := le_n m); unfold m at 1 in Hm.
clearbody m; revert f Hm; induction m as [ | m].
- intros e Hm; destruct e; inversion Hm.
- intros e Hm g1 g2 Hg Hf; destruct e as [c | b | f1 l]; simpl; trivial.
  + simpl in Hf; rewrite Oset.mem_bool_true_iff in Hf.
    apply (Hg _ Hf).
  + simpl in Hf; rewrite Bool.Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
    * rewrite Oset.mem_bool_true_iff in Hf; apply (Hg _ Hf).
    * rewrite Bool.Bool.orb_true_iff; right.
      rewrite forallb_forall; intros x Hx.
      {
        apply IHm with g1; trivial.
        - simpl in Hm; refine (le_trans _ _ _ _ (le_S_n _ _ Hm)).
          apply in_list_size; trivial.
        - rewrite forallb_forall in Hf; apply Hf; trivial.
      }
Qed.

Lemma is_built_upon_ft_incl :
  forall f g1 g2, (forall x, In x g1 -> In x g2) -> 
                  is_built_upon_ft g1 f = true -> is_built_upon_ft g2 f = true.
Proof.
intros f g1 g2 H; apply is_built_upon_ft_trans.
intros x Hx; apply in_is_built_upon_ft; apply H; assumption.
Qed.

Lemma is_built_upon_ft_variables_ft_sub :
  forall f g, 
    is_built_upon_ft g f = true -> variables_ft f subS Fset.Union (A T) (map variables_ft g).
Proof.
intro f.
set (n := size_funterm f).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn; [destruct f; inversion Hn | ].
intros g Hf; destruct f as [c | b | f l]; simpl in Hf; simpl; 
  rewrite Fset.subset_spec; intros a Ha.
- rewrite Fset.empty_spec in Ha; discriminate Ha.
- rewrite Oset.mem_bool_true_iff in Hf.
  rewrite Fset.mem_Union; eexists; split; 
    [rewrite in_map_iff; eexists; split; [ | apply Hf]; apply refl_equal | ]; assumption.
- rewrite Bool.Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
  + rewrite Oset.mem_bool_true_iff in Hf.
  rewrite Fset.mem_Union; eexists; split; 
    [rewrite in_map_iff; eexists; split; [ | apply Hf]; apply refl_equal | ]; assumption.
  + rewrite Fset.mem_Union in Ha.
    destruct Ha as [s [Hs Ha]]; rewrite in_map_iff in Hs.
    destruct Hs as [e [Hs He]]; subst s.
    revert a Ha; rewrite <- Fset.subset_spec; apply IHn.
    * simpl in Hn; refine (le_trans _ _ _ _ (le_S_n _ _ Hn)); apply in_list_size; assumption.
    * rewrite forallb_forall in Hf; apply Hf; assumption.
Qed.

End Sec.

