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
        FTuples FTerms.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Inductive aggterm : Type := 
| A_Expr : funterm T -> aggterm
| A_agg : aggregate T -> funterm T -> aggterm
| A_fun : scalar_operator T -> list aggterm -> aggterm.


Fixpoint size_aggterm (t : aggterm) : nat :=
  match t with
    | A_Expr f 
    | A_agg _ f => S (size_funterm T f)
    | A_fun _ l => S (list_size size_aggterm l)
  end.

Fixpoint aggterm_eq_dec (left right : aggterm) : {left = right} + {left <> right}.
Proof.
decide equality.
all: first
  [ apply (funterm_eq_dec T)
  | apply (aggregate_eq_dec T)
  | apply list_eq_dec; apply aggterm_eq_dec
  | apply (scalar_operator_eq_dec T) ].
Defined.

Definition aggterm_mem := EqDec.mem aggterm_eq_dec.
Definition aggterm_permut : list aggterm -> list aggterm -> Prop :=
  _permut (@eq aggterm).

Lemma aggterm_permut_refl :
  forall terms, aggterm_permut terms terms.
Proof.
intro terms; unfold aggterm_permut.
apply _permut_refl; intros term _; reflexivity.
Qed.

Lemma aggterm_permut_trans :
  forall left middle right,
    aggterm_permut left middle ->
    aggterm_permut middle right ->
    aggterm_permut left right.
Proof.
intros left middle right Hleft Hright; unfold aggterm_permut in *.
apply _permut_trans with middle; [ | exact Hleft | exact Hright].
intros a b c _ _ _ Hab Hbc; subst; reflexivity.
Qed.

Lemma aggterm_mem_true_iff :
  forall term terms, aggterm_mem term terms = true <-> In term terms.
Proof.
intros term terms; unfold aggterm_mem; apply EqDec.mem_true_iff.
Qed.

Lemma aggterm_mem_app :
  forall term left right,
    aggterm_mem term (left ++ right) =
      orb (aggterm_mem term left) (aggterm_mem term right).
Proof.
intros term left right; unfold aggterm_mem; apply EqDec.mem_app.
Qed.

Lemma aggterm_mem_permut :
  forall term left right,
    aggterm_permut left right ->
    aggterm_mem term left = aggterm_mem term right.
Proof.
intros term left right Hpermut; unfold aggterm_mem, aggterm_permut in *.
apply EqDec.mem_permut; assumption.
Qed.

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
  | A_agg _ f => aggterm_mem a1 g || is_built_upon_ft _ (extract_funterms g) f
  | A_fun _ la => aggterm_mem a1 g || forallb (is_built_upon_ag g) la
  end.

Lemma in_is_built_upon_ag :
  forall g f, In f g -> is_built_upon_ag g f = true.
Proof.
intros g f H; destruct f; simpl.
- rewrite <- in_extract_funterms in H; apply in_is_built_upon_ft; assumption.
- rewrite Bool.Bool.orb_true_iff; left; rewrite aggterm_mem_true_iff; assumption.
- rewrite Bool.Bool.orb_true_iff; left; rewrite aggterm_mem_true_iff; assumption.
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
    case_eq (aggterm_mem (A_agg ag f) g1); intro Kf.
    * rewrite aggterm_mem_true_iff in Kf.
      apply Hg; assumption.
    * rewrite Kf, Bool.Bool.orb_false_l in Hf; simpl; rewrite Bool.Bool.orb_true_iff; right.
      revert Hf; apply is_built_upon_ft_trans; intros x Hx.
      rewrite in_extract_funterms in Hx.
      apply (Hg _ Hx).
  + simpl in Hf.
    case_eq (aggterm_mem (A_fun f1 la) g1); intro Kf.
    * rewrite aggterm_mem_true_iff in Kf.
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

Lemma extract_funterms_permut :
  forall left right,
    aggterm_permut left right ->
    funterm_permut (extract_funterms left) (extract_funterms right).
Proof.
intros left right Hpermut.
unfold aggterm_permut in Hpermut; unfold funterm_permut.
induction Hpermut as [|term matched tail prefix suffix Heq _ IH].
- apply Pnil.
- subst matched; rewrite extract_funterms_app; simpl.
  destruct term as [function_term | aggregate function_term | operator arguments].
  + apply Pcons; [reflexivity | ].
    rewrite <- extract_funterms_app; exact IH.
  + rewrite <- extract_funterms_app; exact IH.
  + rewrite <- extract_funterms_app; exact IH.
Qed.

Lemma is_built_upon_ag_permut :
  forall g1 g2 f, aggterm_permut g1 g2 -> is_built_upon_ag g1 f = is_built_upon_ag g2 f.
Proof.
intros g1 g2 f; set (n := size_aggterm f).
assert (Hn := le_n n); unfold n at 1 in Hn; clearbody n.
revert f Hn; induction n as [ | n]; intros f Hn H; [destruct f; inversion Hn | ].
destruct f as [f | a f | f l]; simpl.
- apply is_built_upon_ft_permut.
  apply extract_funterms_permut; assumption.
- apply f_equal2.
  + apply aggterm_mem_permut; assumption.
  + apply is_built_upon_ft_permut.
    apply extract_funterms_permut; assumption.
- apply f_equal2.
   + apply aggterm_mem_permut; assumption.
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
             aggterm_mem (A_agg a f) (map (fun a0 => A_Expr (F_Dot T a0)) l) = false).
{
  intros a _f l.
  case_eq (aggterm_mem (A_agg a _f) (map (fun a0 => A_Expr (F_Dot T a0)) l));
    intro Hmem; [ | reflexivity].
  rewrite aggterm_mem_true_iff, in_map_iff in Hmem.
  destruct Hmem as [attribute [Hconstructor _]]; discriminate Hconstructor.
}
assert (Aux3 : forall f k l, 
             aggterm_mem (A_fun f k) (map (fun a0 => A_Expr (F_Dot T a0)) l) = false).
{
  intros _f k l.
  case_eq (aggterm_mem (A_fun _f k) (map (fun a0 => A_Expr (F_Dot T a0)) l));
    intro Hmem; [ | reflexivity].
  rewrite aggterm_mem_true_iff, in_map_iff in Hmem.
  destruct Hmem as [attribute [Hconstructor _]]; discriminate Hconstructor.
}
destruct f as [c | a | fc lf]; simpl.
- rewrite !extract_funterms_app.
  refine (trans_eq _ (trans_eq (is_built_upon_ft_eq _ _ _ _ _ Hf) _)); 
    rewrite Aux; apply refl_equal.
- rewrite !aggterm_mem_app, !extract_funterms_app, !Aux.
  apply f_equal2; [ | apply is_built_upon_ft_eq; assumption].
  rewrite !Aux2; apply refl_equal.
- apply f_equal2.
  + rewrite !aggterm_mem_app, !Aux3; apply refl_equal.
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

Arguments aggterm_mem {T} _ _.
Arguments aggterm_permut {T} _ _.
Arguments aggterm_permut_refl {T} _.
Arguments aggterm_permut_trans {T} _ _ _ _ _.
