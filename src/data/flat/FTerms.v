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
        OrderedSet DecidableEquality Partition FiniteSet FiniteBag FiniteCollection Join
        FTuples.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.


Inductive funterm : Type :=
| F_Constant : value T -> funterm
| F_Dot : attribute T -> funterm
| F_Expr : scalar_operator T -> list funterm -> funterm.

Fixpoint size_funterm (t : funterm) : nat :=
  match t with
    | F_Constant _
    | F_Dot _ => 1%nat
    | F_Expr _ l => S (list_size size_funterm l)
  end.

Fixpoint funterm_eq_dec (left right : funterm) : {left = right} + {left <> right}.
Proof.
decide equality.
- apply (EqDec.of_oset (OVal T)).
- apply (EqDec.of_oset (OAtt T)).
- apply list_eq_dec; apply funterm_eq_dec.
- apply (scalar_operator_eq_dec T).
Defined.

Definition funterm_mem := EqDec.mem funterm_eq_dec.
Definition funterm_permut : list funterm -> list funterm -> Prop :=
  _permut (@eq funterm).

Lemma funterm_mem_true_iff :
  forall term terms, funterm_mem term terms = true <-> In term terms.
Proof.
intros term terms; unfold funterm_mem; apply EqDec.mem_true_iff.
Qed.

Lemma funterm_mem_app :
  forall term left right,
    funterm_mem term (left ++ right) =
      orb (funterm_mem term left) (funterm_mem term right).
Proof.
intros term left right; unfold funterm_mem; apply EqDec.mem_app.
Qed.

Lemma funterm_mem_permut :
  forall term left right,
    funterm_permut left right ->
    funterm_mem term left = funterm_mem term right.
Proof.
intros term left right Hpermut; unfold funterm_mem, funterm_permut in *.
apply EqDec.mem_permut; assumption.
Qed.

Fixpoint variables_ft (f : funterm) :=
  match f with
  | F_Constant _ => Fset.empty (A T)
  | F_Dot a => Fset.singleton (A T) a
  | F_Expr _ l => Fset.Union (A T) (map variables_ft l)
  end.

Fixpoint is_built_upon_ft g f :=
  match f with
    | F_Constant _ => true
    | F_Dot _ => funterm_mem f g
    | F_Expr _ l => funterm_mem f g || forallb (is_built_upon_ft g) l
  end.

Lemma is_built_upon_ft_unfold :
  forall g f, is_built_upon_ft g f =
  match f with
    | F_Constant _ => true
    | F_Dot _ => funterm_mem f g
    | F_Expr _ l => funterm_mem f g || forallb (is_built_upon_ft g) l
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
intros g f H; destruct f as [v | a | op terms].
- reflexivity.
- change (funterm_mem (F_Dot a) g = true).
  rewrite funterm_mem_true_iff; assumption.
- change (funterm_mem (F_Expr op terms) g || forallb (is_built_upon_ft g) terms = true).
  rewrite Bool.Bool.orb_true_iff; left; rewrite funterm_mem_true_iff; assumption.
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
- rewrite !funterm_mem_app; apply f_equal2; [ | apply refl_equal].
  assert (Hfa : a inS s2 -> a inS s1).
  {
    intros Ha; apply Hf.
    rewrite Fset.mem_inter, Ha, Bool.Bool.andb_true_l; simpl.
    rewrite Fset.singleton_spec, Oset.eq_bool_refl.
    apply refl_equal.
  }
  apply eq_bool_iff; split; intro H; 
    rewrite funterm_mem_true_iff, in_map_iff in H; destruct H as [_a [Ha _H]];
      injection Ha; clear Ha; intro Ha; subst _a.
  + rewrite funterm_mem_true_iff, in_map_iff.
    exists a; split; [apply refl_equal | ].
    apply Fset.mem_in_elements.
    assert (H := Fset.in_elements_mem _ _ _ _H); rewrite Fset.mem_union in H.
    case_eq (a inS? s1); intro Ha1; [apply refl_equal | ].
    rewrite Ha1, Bool.Bool.orb_false_l in H.
    rewrite <- Ha1; apply Hfa; apply H.
  + rewrite funterm_mem_true_iff, in_map_iff.
    exists a; split; [apply refl_equal | ].
    apply Fset.mem_in_elements; rewrite Fset.mem_union.
    rewrite (Fset.in_elements_mem _ _ _ _H); apply refl_equal.
- apply f_equal2.
  + rewrite !funterm_mem_app; apply f_equal2; [ | apply refl_equal].
    rewrite eq_bool_iff; split; intro H;
    rewrite funterm_mem_true_iff, in_map_iff in H; destruct H as [_a [Ha _H]];
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
  forall g1 g2 f, funterm_permut g1 g2 -> is_built_upon_ft g1 f = is_built_upon_ft g2 f.
Proof.
intros g1 g2 f; set (n := size_funterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn H; [destruct f; inversion Hn | ].
destruct f as [c | a | f l]; [apply refl_equal | | ]; simpl.
- apply funterm_mem_permut; assumption.
-  apply f_equal2.
   + apply funterm_mem_permut; assumption.
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
  + simpl in Hf; rewrite funterm_mem_true_iff in Hf.
    apply (Hg _ Hf).
  + simpl in Hf; rewrite Bool.Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
    * rewrite funterm_mem_true_iff in Hf; apply (Hg _ Hf).
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
- rewrite funterm_mem_true_iff in Hf.
  rewrite Fset.mem_Union; eexists; split; 
    [rewrite in_map_iff; eexists; split; [ | apply Hf]; apply refl_equal | ]; assumption.
- rewrite Bool.Bool.orb_true_iff in Hf; destruct Hf as [Hf | Hf].
  + rewrite funterm_mem_true_iff in Hf.
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

Arguments funterm_mem {T} _ _.
Arguments funterm_permut {T} _ _.
