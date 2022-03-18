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

Require Import Arith NArith List.

Require Import BasicFacts ListFacts FiniteSet OrderedSet.

Section Sec.

Hypothesis dom : Type.
Hypothesis symbol : Type.

(** Definition of variables as an type independant from term, in order to be able to build sets of variables *)
Inductive variable : Type :=
  | Vrbl : dom -> N -> variable.

(** Definition of terms *)
Inductive term : Type :=
  | Var : variable -> term 
  | Term : symbol -> list term -> term.

Fixpoint size (t : term) :=
  match t with
    | Var _ => 1
    | Term _ l => S (list_size size l)
  end.

Lemma size_ge_one : forall t, 1 <= size t.
Proof.
intros [v | f l]; [apply le_refl | ].
simpl; apply le_n_S; apply le_O_n.
Qed.

Definition term_rec3 :
  forall (P : term -> Type), 
    (forall v, P (Var v)) -> 
    (forall f l, (forall t, List.In t l -> P t) -> P (Term f l)) ->
    forall t, P t.
Proof.
intros P Hv IH t.
set (n := size t).
assert (Hn := le_n n).
unfold n at 1 in Hn; clearbody n.
revert t Hn; induction n as [ | n].
- intros [v | f l] Hn; [apply Hv | ].
  simpl in Hn; apply False_rect; inversion Hn.
- intros [v | f l] Hn; [apply Hv | ].
  apply IH.
  intros t Ht; apply IHn.
  refine (le_trans _ _ _ (in_list_size size _ _ Ht) _).
  simpl in Hn; apply (le_S_n _ _ Hn).
Defined.


Hypothesis OX : Oset.Rcd variable.
(*
Hypothesis OD : Oset.Rcd dom.
split with 
    (fun x1 x2 => match x1, x2 with 
                | Vrbl d1 x1, Vrbl d2 x2 =>
                    Oeset.compare (mk_oepairs OD (oeset_of_oset ON)) (d1, x1) (d2, x2)
                end);
  try (intros [d1 x1] [d2 x2] [d3 x3]; oeset_compare_tac).
intros [d1 x1] [d2 x2]; oeset_compare_tac.
Defined.
*)

Hypothesis OF : Oset.Rcd symbol.
Hypothesis X : Fset.Rcd OX.

Fixpoint variables_t (t : term) : Fset.set X :=
  match t with
  | Var x => Fset.singleton X x
  | Term _ l => Fset.Union X (map variables_t l)
  end.

Lemma variables_t_unfold :
  forall t, variables_t t = 
  match t with
  | Var x => Fset.singleton X x
  | Term _ l => Fset.Union X (map variables_t l)
  end.
Proof.
unfold_tac.
Qed.

(*
Fixpoint variables_t_list (t : term) :=
  match t with
  | Term _ l => flat_map variables_t_list l
  | Var x => x :: nil
  end.
*)
Lemma in_variables_t_var :
  forall x y, x inS variables_t (Var y) <-> y = x.
Proof.
intros x y; rewrite (variables_t_unfold (Var y)), Fset.singleton_spec, Oset.eq_bool_true_iff.
split; exact (fun h => sym_eq h).
Qed.

(*Lemma variables_t_variables_t_list :
  forall t, variables_t t =S= Fset.mk_set _ (variables_t_list t).
Proof.
intro t; pattern t; apply term_rec3.
- intro v; rewrite Fset.equal_spec; intro x.
  rewrite variables_t_unfold, Fset.singleton_spec.
  rewrite Fset.mem_mk_set; simpl variables_t_list.
  rewrite Oset.mem_bool_unfold, Bool.orb_false_r.
  apply refl_equal.
- intros f l IHl; rewrite Fset.equal_spec; intro x.
  rewrite variables_t_unfold, Fset.mem_mk_set.
  simpl variables_t_list.
  rewrite eq_bool_iff, Fset.mem_Union, Oset.mem_bool_true_iff, in_flat_map; split.
  + intros [s [Hs Hx]].
    rewrite in_map_iff in Hs.
    destruct Hs as [ts [Hs Hts]].
    exists ts; split; [assumption | ].
    assert (IH := IHl _ Hts).
    rewrite Fset.equal_spec in IH.
    subst s; rewrite IH, Fset.mem_mk_set, Oset.mem_bool_true_iff in Hx.
    exact Hx.
  + intros [s [Hs Hx]].
    exists (variables_t s); split.
    * rewrite in_map_iff; exists s; split; trivial.
    * assert (IH := IHl _ Hs).
      rewrite Fset.equal_spec in IH.
      rewrite IH, Fset.mem_mk_set, Oset.mem_bool_true_iff.
      exact Hx.
Qed.
*)

Fixpoint term_compare (t1 t2 : term) : comparison :=
  match t1, t2 with
    | Var v1, Var v2 => Oset.compare OX v1 v2
    | Var _, Term _ _ => Lt
    | Term _ _, Var _ => Gt
    | Term f1 l1, Term f2 l2 =>
      compareAB (Oset.compare OF) (comparelA term_compare) (f1,l1) (f2, l2)
  end.

Lemma term_compare_unfold :
  forall t1 t2, term_compare t1 t2 =
  match t1, t2 with
    | Var v1, Var v2 => Oset.compare OX v1 v2
    | Var _, Term _ _ => Lt
    | Term _ _, Var _ => Gt
    | Term f1 l1, Term f2 l2 =>
      compareAB (Oset.compare OF) (comparelA term_compare) (f1,l1) (f2, l2)
  end.
Proof.
intros t1 t2; case t1; case t2; intros; apply refl_equal.
Qed.

Lemma term_eq_bool_ok :
  forall t1 t2, match term_compare t1 t2 with
             | Eq => t1 = t2
             | _ => t1 <> t2
           end.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2].
  + simpl; oset_compare_tac.
  + simpl; discriminate.
- intros f1 l1 IH [v2 | f2 l2]; [simpl; discriminate | ].
  rewrite term_compare_unfold.
  assert (Aux :  match compareAB (Oset.compare OF) (comparelA term_compare) (f1, l1) (f2, l2) with
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
  destruct (compareAB (Oset.compare OF) (comparelA term_compare) (f1, l1) (f2, l2)).
  + injection Aux; intros; subst; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
  + intro H; injection H; intros; subst; apply Aux; trivial.
Qed.

Lemma term_compare_eq_iff :
  forall t1 t2, term_compare t1 t2 = Eq <-> t1 = t2.
Proof.
intros t1 t2; generalize (term_eq_bool_ok t1 t2).
case (term_compare t1 t2).
- intros; subst; split; trivial.
- intro H; split; try discriminate.
  intro; subst; apply False_rec; apply H; trivial.
- intro H; split; try discriminate.
  intro; subst; apply False_rec; apply H; trivial.
Qed.

(*
Lemma term_compare_lt_trans :
  forall t1 t2 t3, term_compare t1 t2 = Lt -> term_compare t2 t3 = Lt -> term_compare t1 t3 = Lt.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial)).
  oset_compare_tac.
- intros f1 l1 IH [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial; fail)).
  rewrite 3 term_compare_unfold.
  compareAB_tac; try oset_compare_tac.
  comparelA_tac.
  + oset_compare_tac.
  + 
  case_eq (Oset.compare OF f1 f2); intro Hf12.
  + generalize (Oset.eq_bool_ok OF f1 f2); rewrite Hf12; intro; subst f2; clear Hf12.
    intros Hl1.
    case (Oset.compare OF f1 f3); trivial.
    revert Hl1; refine (comparelA_lt_trans _ _ _ _ _ _ _ _).
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a2 a3); rewrite Ha23; intro; subst a2.
      assumption.
    * do 6 intro; apply IH; trivial.
  + intros _; case_eq (Oset.compare OF f2 f3); intro Hf23.
    * rewrite (Oset.compare_lt_eq_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * rewrite (Oset.compare_lt_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * intro Abs; discriminate Abs.
  + intro Abs; discriminate Abs.
Qed.
*)


Lemma term_compare_lt_trans :
  forall t1 t2 t3, term_compare t1 t2 = Lt -> term_compare t2 t3 = Lt -> term_compare t1 t3 = Lt.
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial)).
  apply Oset.compare_lt_trans.
- intros f1 l1 IH [v2 | f2 l2] [v3 | f3 l3]; try (discriminate || (simpl; trivial)).
  case_eq (Oset.compare OF f1 f2); intro Hf12.
  + generalize (Oset.eq_bool_ok OF f1 f2); rewrite Hf12; intro; subst f2; clear Hf12.
    intros Hl1.
    case (Oset.compare OF f1 f3); trivial.
    revert Hl1; refine (comparelA_lt_trans _ _ _ _ _ _ _ _).
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a1 a2); rewrite Ha12; intro; subst a2.
      assumption.
    * do 6 intro; intros Ha12 Ha23.
      generalize (term_eq_bool_ok a2 a3); rewrite Ha23; intro; subst a2.
      assumption.
    * do 6 intro; apply IH; trivial.
  + intros _; case_eq (Oset.compare OF f2 f3); intro Hf23.
    * rewrite (Oset.compare_lt_eq_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * rewrite (Oset.compare_lt_trans _ _ _ _ Hf12 Hf23).
      intros _; apply refl_equal.
    * intro Abs; discriminate Abs.
  + intro Abs; discriminate Abs.
Qed.

Lemma term_compare_lt_gt :
  forall t1 t2, term_compare t1 t2 = CompOpp (term_compare t2 t1).
Proof.
intro t1; pattern t1; apply term_rec3; clear t1.
- intros v1 [v2 | f2 l2]; simpl; [ | trivial].
  apply Oset.compare_lt_gt.
- intros f1 l1 IH [v2 | f2 l2]; simpl; [trivial | ].
  rewrite (Oset.compare_lt_gt OF f2 f1).
  case (Oset.compare OF f1 f2); simpl; trivial.
  refine (comparelA_lt_gt _ _ _ _).
  do 4 intro; apply IH; assumption.
Qed.

Definition OT : Oset.Rcd term.
split with term_compare.
- apply term_eq_bool_ok.
- apply term_compare_lt_trans.
- apply term_compare_lt_gt.
Defined.

End Sec.

Arguments Var {dom} {symbol} x.
