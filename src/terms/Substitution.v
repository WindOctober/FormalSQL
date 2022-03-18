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

(** * Substitutions in a term algebra.*)

Require Import List Arith NArith Max Bool.

Require Import BasicFacts OrderedSet FiniteSet ListFacts ListSet Term.

Section Sec.
Hypothesis dom : Type.
Hypothesis symbol : Type.

Hypothesis OX : Oset.Rcd (variable dom).
Hypothesis X : Fset.Rcd OX.

Hypothesis OF : Oset.Rcd symbol.

Notation variable := (variable dom).
Notation term := (term dom symbol).

Definition substitution : Type := list (variable * term).

Fixpoint apply_subst (sigma : substitution) (t : term) {struct t} : term :=
  match t with
    | Var v => 
      match Oset.find OX v sigma with
        | None => t
        | Some v_sigma => v_sigma
      end
    | Term f l => Term f (map (apply_subst sigma) l)
  end.

Definition domain_of_subst (sigma : substitution) := Fset.mk_set X (List.map (@fst _ _) sigma).
Definition codomain_of_subst (sigma : substitution) := 
  Fset.Union X (List.map (fun t => variables_t X (@snd _ _ t)) sigma).

Lemma apply_subst_unfold :
  forall sigma t, 
    apply_subst sigma t =   
    match t with
      | Var v => 
        match Oset.find OX v sigma with
          | None => t
          | Some v_sigma => v_sigma
        end
      | Term f l => Term f (map (apply_subst sigma) l)
    end.
Proof.
intros sigma t; case t; intros; apply refl_equal.
Qed.

Lemma domain_of_subst_unfold :
  forall x t sigma, domain_of_subst ((x, t) :: sigma) = Fset.add _ x (domain_of_subst sigma).
Proof.
intros x t sigma; unfold domain_of_subst; simpl; apply refl_equal.
Qed.

Lemma domain_of_subst_inv :
forall sigma f,
  domain_of_subst 
    (map
       (fun zt : variable * term =>
          let (z, t) := zt in (z, f t)) sigma) =S= domain_of_subst sigma.
Proof.
intros sigma f; rewrite Fset.equal_spec; intro z; unfold domain_of_subst.
rewrite map_map; do 2 apply f_equal.
rewrite <- map_eq.
intros a _; destruct a; trivial.
Qed.

Lemma empty_subst_is_id : forall t, apply_subst nil t = t.
Proof.
intro t; pattern t; apply term_rec3; clear t; trivial.
intros f l IH; simpl; apply (f_equal (fun l => Term f l));
induction l as [ | t l]; trivial; simpl; rewrite (IH t).
rewrite IHl; trivial.
intros; apply IH; right; trivial.
left; trivial.
Qed.

Lemma apply_subst_eq_1 :
  forall t sigma sigma', 
    (forall v, v inS variables_t X t -> 
               apply_subst sigma (Var v) = apply_subst sigma' (Var v)) <-> 
  apply_subst sigma t = apply_subst sigma' t.
Proof.
  intros t sigma sigma'; split.
  - pattern t; apply term_rec3; clear t.
    + intros v H; apply H; rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff.
      apply refl_equal.
    + intros f l IHl H.
      simpl; apply (f_equal (fun l => Term f l)).
      rewrite <- map_eq; intros t t_in_l; apply IHl; trivial.
      intros v v_in_t; apply H.
      rewrite variables_t_unfold, Fset.mem_Union.
      exists (variables_t X t); split; trivial.
      rewrite in_map_iff; exists t; split; trivial.
  - pattern t; apply term_rec3; clear t.
    + intros v H x x_eq_v.
      rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff in x_eq_v; subst v.
      assumption.
    + intros f l IHl H; simpl in H; injection H; clear H; intro H.
      intros v v_in_l; rewrite variables_t_unfold, Fset.mem_Union in v_in_l.
      destruct v_in_l as [s [Hs Hv]].
      rewrite in_map_iff in Hs; destruct Hs as [t [Hs Ht]]; subst s.
      apply (IHl t Ht); [ | assumption].
      rewrite <- map_eq in H; apply H; assumption.
Qed.

Lemma apply_subst_outside_dom :
  forall sigma t, (domain_of_subst sigma interS variables_t X t) =S= (emptysetS) ->
                  apply_subst sigma t = t.
Proof.
intros sigma t H; apply eq_trans with (apply_subst nil t); [ | apply empty_subst_is_id].
rewrite <- apply_subst_eq_1.
intros v Hv; rewrite 2 apply_subst_unfold.
case_eq (Oset.find OX v sigma); [ | intros; apply refl_equal].
intros u Hu.
assert (Abs : v inS (Fset.empty X)).
{
  rewrite <- (Fset.mem_eq_2 _ _ _ H), Fset.mem_inter, Hv, Bool.andb_true_r.
  unfold domain_of_subst; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  exists (v, u); split; trivial.
  apply (Oset.find_some _ _ _ Hu).
}
rewrite Fset.empty_spec in Abs; discriminate Abs.
Qed.

Lemma var_in_apply_subst :
  forall x sigma t, x inS (variables_t X (apply_subst sigma t)) <->
                    (exists x', x' inS variables_t X t /\ 
                               x inS (variables_t X (apply_subst sigma (Var x')))).
Proof.
intros x sigma t; pattern t; apply term_rec3; clear t; [intro v | intros f l IHl]; split.
- intros H; exists v; split; trivial.
  rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff; apply refl_equal.
- intros [x' [Hx' Hx]].
  rewrite variables_t_unfold, Fset.singleton_spec in Hx'.
  rewrite Oset.eq_bool_true_iff in Hx'; subst v.
  assumption.
- intro Hx.
  rewrite apply_subst_unfold, variables_t_unfold, Fset.mem_Union in Hx.
  destruct Hx as [s [Hs Hx]].
  rewrite map_map, in_map_iff in Hs.
  destruct Hs as [t [Hs Ht]]; subst s.
  rewrite (IHl _ Ht) in Hx.
  destruct Hx as [x' [Hx' Kx']].
  exists x'; split; trivial.
  rewrite variables_t_unfold, Fset.mem_Union.
  exists (variables_t X t); split; trivial.
  rewrite in_map_iff; exists t; split; trivial.
- intros [x' [Hx' Hx]].
  rewrite apply_subst_unfold, variables_t_unfold, map_map.
  rewrite Fset.mem_Union.
  rewrite variables_t_unfold, Fset.mem_Union in Hx'.
  destruct Hx' as [s [Hs Hx']].
  rewrite in_map_iff in Hs; destruct Hs as [t [Hs Ht]]; subst s.
  exists (variables_t X (apply_subst sigma t)).
  split; [rewrite in_map_iff; exists t; split; trivial | ].
  rewrite IHl; [ | assumption].
  exists x'; split; trivial.
Qed.

Lemma var_not_in_apply_renaming_term :
  forall x y t, x <> y ->  
                x inS? (variables_t X (apply_subst ((x, Var y) :: nil) t)) = false.
Proof.
intros x y t x_diff_y; pattern t; apply term_rec3; clear t.
- intros v; simpl.
  case_eq (Oset.eq_bool OX v x); intro Hv.
  + rewrite Oset.eq_bool_true_iff in Hv; subst v.
    rewrite <- not_true_iff_false, in_variables_t_var; intro; subst; apply x_diff_y; trivial.
  + rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_sym; assumption.
- intros f l IH; rewrite apply_subst_unfold, variables_t_unfold, map_map, <- not_true_iff_false.
  rewrite Fset.mem_Union; intros [s [Hs Hx]].
  rewrite in_map_iff in Hs; destruct Hs as [t [Hs Ht]]; subst s.
  rewrite (IH _ Ht) in Hx; discriminate Hx.
Qed.

Lemma apply_subst_apply_subst : 
  forall sigma1 sigma2 t,
   apply_subst sigma1 (apply_subst sigma2 t) = 
   apply_subst (map (fun xt => (fst xt, apply_subst sigma1 (snd xt))) sigma2 ++ sigma1) t.
Proof.
intros sigma1 sigma2 t; pattern t; apply term_rec3; clear t.
- intro v; simpl.
  rewrite Oset.find_app.
  case_eq (Oset.find OX v sigma2).
  + intros t Ht.
    replace (Oset.find OX v
                       (map
                          (fun xt : variable * term =>
                             (fst xt, apply_subst sigma1 (snd xt))) sigma2)) with
    (Some (apply_subst sigma1 t)); [apply refl_equal | ].
    induction sigma2 as [ | [x1 t1] sigma2]; [discriminate Ht | ].
    simpl in Ht; simpl; destruct (Oset.eq_bool OX v x1).
    * injection Ht; clear Ht; intro Ht; subst; trivial.
    * apply IHsigma2; trivial.
  + intro Hv; simpl.
    replace (Oset.find OX v
                       (map
                          (fun xt : variable * term =>
                             (fst xt, apply_subst sigma1 (snd xt))) sigma2)) with (@None term);
      [apply refl_equal | ].
    induction sigma2 as [ | [x1 t1] sigma2]; [trivial | ].
    simpl in Hv; simpl; destruct (Oset.eq_bool OX v x1); [discriminate Hv | ].
    apply IHsigma2; trivial.
- intros f l IHl; simpl; apply f_equal.
  rewrite map_map, <- map_eq.
  intros t Ht; apply IHl; assumption.
Qed.

Definition renaming : Type := list (variable * variable).

Fixpoint apply_renaming (rho : renaming) (t : term) {struct t} : term :=
  match t with
    | Var v => 
      match Oset.find OX v rho with
        | None => t
        | Some v' => Var v'
      end
    | Term f l => Term f (map (apply_renaming rho) l)
  end.

Definition domain_of_renaming (rho : renaming) := Fset.mk_set X (List.map (@fst _ _) rho).
Definition codomain_of_renaming (rho : renaming) := 
  Fset.mk_set X (List.map (fun x => (@snd _ _ x)) rho).

Lemma apply_renaming_unfold :
  forall rho t, 
    apply_renaming rho t =   
    match t with
      | Var v => 
        match Oset.find OX v rho with
          | None => t
          | Some v' => Var v'
        end
      | Term f l => Term f (map (apply_renaming rho) l)
    end.
Proof.
intros rho t; case t; intros; apply refl_equal.
Qed.

Definition substitution_of_renaming (rho : renaming) : substitution :=
  List.map (fun xx => match xx with (x, x') => (x, Var x') end) rho.

Lemma domain_of_subst_of_renaming :
  forall rho, domain_of_subst (substitution_of_renaming rho) = domain_of_renaming rho.
Proof.
intro rho; unfold substitution_of_renaming, domain_of_subst, domain_of_renaming.
apply f_equal.
rewrite map_map; rewrite <- map_eq; intros [x y] H; apply refl_equal.
Qed.

Lemma codomain_of_subst_of_renaming :
  forall rho, codomain_of_subst (substitution_of_renaming rho) =S= codomain_of_renaming rho.
Proof.
intro rho; unfold substitution_of_renaming, codomain_of_subst, codomain_of_renaming.
rewrite Fset.equal_spec; intro x.
rewrite map_map, eq_bool_iff, Fset.mem_Union, Fset.mem_mk_set, Oset.mem_bool_true_iff; split.
- intros [s [Hs Hx]]; rewrite in_map_iff in Hs.
  destruct Hs as [[y z] [Hs H]]; subst s.
  simpl snd in Hx; rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff in Hx.
  subst z; rewrite in_map_iff.
  exists (y, x); split; trivial.
- intro H; rewrite in_map_iff in H.
  destruct H as [[y _x] [Hx H]]; simpl in Hx; subst _x.
  exists (variables_t X (snd (let (x1, x') := (y, x) in (x1, @Var _ symbol x')))); split.
  + rewrite in_map_iff; exists (y, x); split; trivial.
  + simpl snd; rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff.
    apply refl_equal.
Qed.

Lemma apply_subst_substitution_of_renaming :
  forall t rho, apply_subst (substitution_of_renaming rho) t = apply_renaming rho t.
Proof.
intros t; pattern t; apply term_rec3; clear t.
- intros v rho; unfold substitution_of_renaming.
  simpl; induction rho as [ | [x1 y1] rho]; [apply refl_equal | simpl].
  case (Oset.eq_bool OX v x1); [apply refl_equal | apply IHrho].
- intros f l IH rho; simpl.
  apply f_equal; rewrite <- map_eq; intros t Ht; apply IH; assumption.
Qed.

(** Removing useless bindings in substitutions. *)
Definition clean_subst (sigma : substitution) :=
  map (fun x => (x, apply_subst sigma (Var x))) ({{{domain_of_subst sigma}}}).

Lemma clean_subst_unfold :
  forall sigma, 
    clean_subst sigma = 
    map (fun x => (x, apply_subst sigma (Var x))) ({{{domain_of_subst sigma}}}).
Proof.
intro sigma; apply refl_equal.
Qed.

Lemma find_clean_subst :
  forall sigma x, Oset.find OX x (clean_subst sigma) = Oset.find OX x sigma.
Proof.
intros sigma x; unfold clean_subst.
case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
- assert (Kx : x inS domain_of_subst sigma).
  {
    unfold domain_of_subst; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    exists (x, x_val); split; trivial.
    apply (Oset.find_some _ _ _ x_sigma).
  }
  generalize (Fset.mem_in_elements _ _ _ Kx); clear Kx; intro Kx.
  set (l := ({{{domain_of_subst sigma}}})) in *; clearbody l.
  induction l as [ | v1 l]; [contradiction Kx | ].
  simpl in Kx.
  case_eq (Oset.eq_bool OX x v1); intro Jx.
  + rewrite Oset.eq_bool_true_iff in Jx; subst v1.
    simpl; rewrite Oset.eq_bool_refl, x_sigma; trivial.
  + destruct Kx as [Kx | Kx]; [subst v1; rewrite Oset.eq_bool_refl in Jx; discriminate Jx | ].
    simpl; rewrite Jx; apply IHl; trivial.
- case_eq (Oset.find OX x
                     (map (fun x0 : variable => (x0, apply_subst sigma (Var x0)))
                          ({{{domain_of_subst sigma}}}))); [ | intros; trivial].
  intros s Hs; apply False_rec.
  generalize (Oset.find_some _ _ _ Hs); clear Hs.
  rewrite in_map_iff.
  intros [_x [Hx Kx]]; injection Hx; clear Hx; do 2 intros; subst _x s.
  generalize (Fset.in_elements_mem _ _ _ Kx); clear Kx; intro Kx.
  unfold domain_of_subst in Kx; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Kx.
  destruct Kx as [[_x s] [_Hx Kx]]; simpl in _Hx; subst _x.
  apply (Oset.find_none _ _ _ x_sigma _ Kx).
Qed.
 
Lemma clean_subst_eq :
  forall sigma t, apply_subst (clean_subst sigma) t = apply_subst sigma t.
Proof.
intros sigma t; rewrite <- apply_subst_eq_1.
intros v Hv; simpl; rewrite find_clean_subst; trivial.
Qed.

Lemma clean_subst_cleaned_1 :
  forall sigma x t, In (x,t) (clean_subst sigma) -> apply_subst sigma (Var x) = t.
Proof.
intros sigma x t H.
unfold clean_subst in H; rewrite in_map_iff in H.
destruct H as [_x [H Hx]].
injection H; clear H; do 2 intro; subst _x t; apply refl_equal.
Qed.

Lemma clean_subst_cleaned_2 :
  forall sigma x t, Oset.find OX x sigma = Some t -> In (x,t) (clean_subst sigma).
Proof.
intros sigma x t H.
unfold clean_subst; rewrite in_map_iff.
exists x; simpl; rewrite H; split; trivial.
apply Fset.mem_in_elements; unfold domain_of_subst.
rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
exists (x, t); split; trivial.
apply (Oset.find_some _ _ _ H).
Qed.

Lemma clean_subst_cleaned :
  forall sigma x t, Oset.find OX x sigma = Some t <-> In (x,t) (clean_subst sigma).
Proof.
intros sigma x t; split.
- apply clean_subst_cleaned_2.
- intro H.
  generalize (clean_subst_cleaned_1 _ _ _ H); simpl.
  case_eq (Oset.find OX x sigma).
  + intros _t _H _Ht; subst _t; apply refl_equal.
  + intros _H; apply False_rec.
    unfold clean_subst in H; rewrite in_map_iff in H.
    destruct H as [_x [H Hx]].
    injection H; clear H; do 2 intro; subst _x t.
    generalize (Fset.in_elements_mem _ _ _ Hx); clear Hx; intro Hx.
    unfold domain_of_subst in Hx.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Hx.
    destruct Hx as [[_x t] [_Hx Hx]]; simpl in _Hx; subst _x.
    apply (Oset.find_none _ _ _ _H _ Hx).
Qed.


Section Fresh.

Fixpoint maxN l :=
  match l with
    | nil => 0%N
    | n1 :: l1 => N.max n1 (maxN l1)
  end.

Lemma le_maxN :
  forall n l, In n l -> (n <= maxN l)%N.
Proof.
intros n l; induction l; intro H; [contradiction H | ].
simpl; simpl in H; destruct H as [H | H].
- subst a; apply N.le_max_l.
- refine (N.le_trans _ _ _ _ (N.le_max_r _ _)).
  apply IHl; assumption.
Qed.

Fixpoint max_t (t : term) :=
  match t with
    | Var (Vrbl _ n) => n
    | Term _ l => maxN (map max_t l)
  end.

Definition max_s s := maxN (map (fun x => match x with Vrbl _ n => n end) (Fset.elements X s)).

Fixpoint shift_term M (t : term) :=
  match t with
    | Var (Vrbl x n) => Var (Vrbl x (M+n)%N)
    | Term f l => Term f (map (shift_term M) l)
  end.

Definition shift_subst M (sigma : substitution) :=
  map (fun xt => match xt with (x, t) => (x, shift_term M t) end) sigma.

End Fresh.

(*
Lemma var_in_domain_of_subst :
  forall v sigma,
   FSet.mem FX v (domain_of_subst sigma) = true <-> (find X v sigma <> None).
Proof.
intros v sigma; induction sigma as [ | [x t] sigma]; simpl; split; intro H.
- rewrite FSet.elements_spec2, FSet.elements_empty in H; discriminate H.
- apply False_rec; apply H; reflexivity.
- generalize (DType.eq_bool_ok X v x); case (DType.eq_bool X v x); [intro v_eq_x | intro v_diff_x].
  + discriminate.
  + rewrite <- IHsigma.
    rewrite FSet.add_spec, Bool.orb_true_iff in H.
    destruct H as [v_eq_x | v_in_dom]; [ | assumption].
    apply False_rec; apply v_diff_x.
    generalize (DType.eq_bool_ok (FSet.Elt FX) v x); rewrite v_eq_x; exact (fun h => h).
- revert H; generalize (DType.eq_bool_ok X v x); case (DType.eq_bool X v x); [intros v_eq_x _ | intros v_diff_x H].
  + rewrite FSet.add_spec, v_eq_x, DType.eq_bool_refl; apply refl_equal.
  + rewrite <- IHsigma in H.
    rewrite FSet.add_spec, H, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma subst_remove_var : 
  forall x t s, var_in_term X x t = false -> var_in_term X x (apply_subst ((x, t) :: nil) s) = false.
Proof.
intros x t s H; pattern s; apply term_rec3; clear s.
(* 1/2 *)
intros v; simpl.
case_eq (DType.eq_bool X v x); [intro v_eqb_x; apply H | intro v_diffb_x; simpl; rewrite v_diffb_x; apply refl_equal].
(* 1/1 *)
intros f l IH; simpl; induction l as [ | s l]; simpl.
unfold var_in_term_list; simpl; apply refl_equal.
rewrite var_in_term_list_unfold, (IH s (or_introl _ (refl_equal _))); simpl.
apply IHl; intros; apply IH; right; assumption.
Qed.

Lemma subst_not_remove_var :
   forall x t y s,  var_in_term X y t = false -> var_in_term X y s = false -> 
   var_in_term X y (apply_subst ((x,t) :: nil) s) = false.
Proof.
intros x t y s H; pattern s; apply term_rec3; clear s.
(* 1/2 *)
intros v y_not_in_v; simpl; case (DType.eq_bool X v x); assumption.
(* 1/1 *)
intros f l IH; simpl.
induction l as [ | s l]; simpl.
exact (fun h => h).
rewrite 2 var_in_term_list_unfold.
intro K; rewrite Bool.orb_false_iff in K; destruct K as [K1 K2].
rewrite (IH s (or_introl _ (refl_equal _))); simpl.
apply IHl.
intros; apply IH; [right | ]; assumption.
assumption.
assumption.
Qed.

Lemma apply_subst_app_left :
  forall (t : term) tau1 tau2, (forall x, var_in_term X x t = true -> In x (map (@fst _ _) tau1)) ->
  apply_subst (tau1 ++ tau2) t = apply_subst tau1 t.
Proof.
intros t tau1 tau2 H; rewrite <- subst_eq_vars.
intros x x_in_t; simpl; rewrite find_app2; case_eq (find X x tau1); [intros tx Hx; simpl in Hx; rewrite Hx; apply refl_equal | intro Hx].
assert (Kx := H _ x_in_t).
rewrite in_map_iff in Kx; destruct Kx as [[x' t'] [x_eq_x' Jx]]; simpl in x_eq_x'; subst x'.
apply False_rec; apply (find_not_found X x x t' tau1 Hx (DType.eq_bool_refl X _) Jx).
Qed.

Lemma apply_subst_app_right :
  forall (t : term) tau1 tau2, (forall x, var_in_term X x t = true -> In x (map (@fst _ _) tau1) -> False) ->
  apply_subst (tau1 ++ tau2) t = apply_subst tau2 t.
Proof.
intros t tau1 tau2 H; rewrite <- subst_eq_vars.
intros x x_in_t; simpl; rewrite find_app2; case_eq (find (DType.eq_bool X) x tau1); [intros tx Hx | intro Hx; apply refl_equal].
apply False_rec; apply (H _ x_in_t).
rewrite in_map_iff; exists (x, tx); split.
apply refl_equal.
destruct (find_mem _ _ _ Hx) as [x' [l1 [l2 [x_eq_x' Kx]]]].
rewrite DType.eq_bool_true in x_eq_x'; subst x'; rewrite Kx; apply in_or_app; right; left; apply refl_equal.
Qed.


Lemma remove_garbage_subst_aux1 :
  forall sigma  cleaned_sig : substitution, 
  let sigma' := clean_subst cleaned_sig sigma in
  forall x, find (DType.eq_bool X) x (cleaned_sig ++ sigma) = find (DType.eq_bool X) x sigma'.
Proof.
intro sigma; induction sigma as [ | [x t] sigma]; simpl.
intros tau x; rewrite <- app_nil_end; apply refl_equal.
intros tau y; rewrite find_app2; simpl.
case_eq (mem_bool X x (map (fun st : variable * term => fst st) tau)); intro H; simpl in H; rewrite H.
(* 1/2 *)
rewrite <- IHsigma, find_app2; simpl.
case_eq (find X y tau); [intros ty Hy; simpl in Hy; rewrite Hy; apply refl_equal | intro Hy].
generalize (DType.eq_bool_ok X y x); case (DType.eq_bool X y x); [intro y_eq_x; subst | intros _; apply refl_equal].
assert (K := mem_bool_ok X x (map (fun st : variable * term => fst st) tau)).
simpl in K; rewrite H in K; simpl Brel.R in K.
assert (J := mem_impl_in _ _ K).
rewrite in_map_iff in J; destruct J as [[x' s] [x_eq_x' J]]; simpl in x_eq_x'; subst x'.
apply False_rec; apply (find_not_found X x x s _ Hy (DType.eq_bool_refl X _) J).
(* 1/1 *)
rewrite <- IHsigma, find_app2; simpl.
generalize (DType.eq_bool_ok X y x); case (DType.eq_bool X y x); [intro y_eq_x; subst | intros _; apply refl_equal].
case_eq (find X x tau); [intros tx Hx | intro Hx;  simpl in Hx; rewrite Hx; apply refl_equal].
destruct (find_mem X _ _ Hx) as [x' [l1 [l2 [x_eq_x' K]]]].
simpl in x_eq_x'; rewrite DType.eq_bool_true in x_eq_x'; subst x'.
rewrite K, map_app, mem_bool_app in H; simpl in H.
rewrite (DType.eq_bool_refl X), Bool.orb_true_r in H; discriminate.
Qed.

Lemma remove_garbage_subst_aux2 :
  forall sigma  cleaned_sig : substitution, 
  let sigma' := clean_subst cleaned_sig sigma in
  ((forall x val, In (x,val) cleaned_sig -> find (DType.eq_bool X) x cleaned_sig = Some val) /\
   (forall x y val val' (tau tau' tau'' : substitution), 
   cleaned_sig = tau ++ (x,val) :: tau' ++ (y,val') :: tau'' -> x <> y)) ->
   
   ((forall x val, In (x,val) sigma' -> find (DType.eq_bool X) x sigma' = Some val) /\
   (forall x y val val' (tau tau' tau'' : substitution), 
   sigma' = tau ++ (x,val) :: tau' ++ (y,val') :: tau'' -> x <> y)).
Proof.
induction sigma as [ | [x t] sigma]; intros tau sigma' [H1 H2].
split.
(* 1/3 *)
simpl in sigma'; subst sigma'; assumption.
(* 1/2 *)
simpl in sigma'; subst sigma'; assumption.
(* 1/1 *)
simpl in sigma'; subst sigma'.
case_eq (mem_bool (DType.eq_bool X) x (map (fun st : variable * term => fst st) tau)); intro H.
(* 1/2 *)
split.
refine ((proj1 (IHsigma _ _))); split; assumption.
refine ((proj2 (IHsigma _ _))); split; assumption.
(* 1/1 *)
split.
refine ((proj1 (IHsigma _ _))); split.
(* 1/3 *)
simpl; intros z u [H3 | H3].
injection H3; clear H3; intros; subst; rewrite (DType.eq_bool_refl X); apply refl_equal.
generalize (DType.eq_bool_ok X z x); case (DType.eq_bool X z x); [intro z_eq_x; subst z | intro z_diff_x].
assert (H4 : In x (map (fun st : variable * term => fst st) tau)).
rewrite in_map_iff; exists (x, u); split; [apply refl_equal | assumption ].
rewrite (in_impl_mem_bool X _ _ H4) in H; discriminate.
apply H1; assumption.
(* 1/2 *)
intros x1 x2 t1 t2 [ | [x3 t3] tau1] tau2 tau3 K; simpl in K; injection K; clear K; intros K1 K2 K3.
intro K4; subst; revert H.
rewrite map_app, mem_bool_app; simpl; rewrite (DType.eq_bool_refl X x2), Bool.orb_true_r; discriminate.
subst t3 x3; revert K1; apply H2.
(* 1/1 *)
refine ((proj2 (IHsigma _ _))); split.
simpl; intros z u [H3 | H3].
injection H3; clear H3; intros; subst; rewrite (DType.eq_bool_refl X); apply refl_equal.
generalize (DType.eq_bool_ok X z x); case (DType.eq_bool X z x); [intro z_eq_x; subst z | intro z_diff_x].
assert (H4 : In x (map (fun st : variable * term => fst st) tau)).
rewrite in_map_iff; exists (x, u); split; [apply refl_equal | assumption ].
rewrite (in_impl_mem_bool X _ _ H4) in H; discriminate.
apply H1; assumption.
(* 1/1 *)
intros x1 x2 t1 t2 [ | [x3 t3] tau1] tau2 tau3 K; simpl in K; injection K; clear K; intros K1 K2 K3.
intro K4; subst; revert H.
rewrite map_app, mem_bool_app; simpl; rewrite (DType.eq_bool_refl X x2), Bool.orb_true_r; discriminate.
subst t3 x3; revert K1; apply H2.
Qed.

Lemma remove_garbage_subst :
  forall sigma, 
  let sigma' := clean_subst nil sigma in
   ((forall x, find (DType.eq_bool X) x sigma = find (DType.eq_bool X) x sigma') /\
   (forall x val, In (x,val) sigma' -> find (DType.eq_bool X) x sigma' = Some val) /\
   (forall x y val val' (tau tau' tau'' : substitution), 
   sigma' = tau ++ (x,val) :: tau' ++ (y,val') :: tau'' -> x <> y)).
Proof.
intros sigma sigma'; subst sigma'; split.
intro x; rewrite <- remove_garbage_subst_aux1; apply refl_equal.
apply remove_garbage_subst_aux2; split.
intros; contradiction.
intros x1 x2 t1 t2 [ | [x3 t3] tau1] tau2 tau3 H; discriminate.
Qed.

(** Composition of substitutions. *)
Definition map_subst (f : variable * term -> term) sigma :=
  map (fun xval => (@fst variable _ xval, f xval)) sigma.

Lemma domain_of_subst_map_subst :
 forall sigma f, domain_of_subst (map_subst f sigma) = domain_of_subst sigma.
Proof.
intros sigma f; 
induction sigma as [ | [x t] sigma]; simpl; trivial; rewrite IHsigma; trivial.
Qed.

Definition subst_comp sigma1 sigma2 :=
  (map_subst (fun xt => apply_subst sigma1 (snd xt)) sigma2)
  ++ 
  (map_subst (fun vt =>
                        match find (DType.eq_bool X) (fst vt) sigma2 with
                        | None => snd vt
                        | Some v_sigma2 => apply_subst sigma1 v_sigma2
                        end)
                      sigma1).

Lemma subst_comp_is_subst_comp_aux1 :
  forall v sigma f,
  find X v (map_subst f sigma) =
   match find X v sigma with
   | None => None
   | Some t => Some (f (v, t))
  end.
Proof.
intros v sigma f; induction sigma as [ | [v1 a1] sigma]; simpl.
reflexivity.
generalize (DType.eq_bool_ok X v v1); case (DType.eq_bool X v v1).
intro v_eq_v1; subst v1; reflexivity.
intros _; apply IHsigma.
Qed.

Lemma subst_comp_is_subst_comp_aux2 :
  forall v sigma1 sigma2,
  find (B:= term) X v (sigma1 ++ sigma2)  =
  match find X v sigma1 with
  | Some _ => find X v sigma1
  | None => find X v sigma2
  end.
Proof.
fix 2.
intros v sigma1 sigma2; case sigma1; clear sigma1.
reflexivity.
intros p sigma; case p; clear p; intros v1 a1; simpl.
case (DType.eq_bool X v v1).
reflexivity.
apply subst_comp_is_subst_comp_aux2.
Qed.


Definition subst_rest (cond : variable -> bool) sigma : substitution :=
  List.filter (fun xt => cond (fst xt)) sigma.

Lemma subst_rest_ok :
  forall cond sigma v, cond v = true -> 
  apply_subst (subst_rest cond sigma) (Var _ v) = apply_subst sigma (Var _ v).
Proof.
fix 2.
intros cond sigma; case sigma; clear sigma.
intros v _; apply refl_equal.
intros p sigma; case p; clear p.
intros z t v cond_v; simpl; generalize (DType.eq_bool_ok X v z); case_eq (DType.eq_bool X v z); 
[intros v_eq_z v_eq_z_bool; subst z; rewrite cond_v | intros v_diff_z_bool v_diff_z].
simpl; rewrite (DType.eq_bool_refl X); apply refl_equal.
case (cond z); simpl; [rewrite v_diff_z_bool |]; apply subst_rest_ok; assumption.
Qed.

Lemma resize_dom : 
  forall sigma (l : list term),
  exists sigma',
  (forall x, var_in_term_list X x l = true ->
             apply_subst sigma (Var _ x) = apply_subst sigma' (Var symbol x)) /\ 
  (forall x, var_in_term_list X x l = true <-> 
                           In x (map (@fst _ _) sigma')).
Proof.
intros sigma l.
assert (H : exists l', forall x, var_in_term_list X x l = true <-> In x l').
induction l as [ | t l].
exists nil; intros; split; intro H; [discriminate | contradiction].
destruct IHl as [l' IH].
exists ((var_list t) ++ l'); split; intro H.
rewrite var_in_term_list_unfold in H; apply in_or_app.
destruct (Bool.orb_true_elim _ _ H) as [H1 | H1]; clear H.
left; rewrite <- (var_list_is_sound X x t); assumption.
right; rewrite <- IH; assumption.
rewrite var_in_term_list_unfold.
destruct (in_app_or _ _ _ H) as [H1 | H1]; clear H.
rewrite <- (var_list_is_sound X) in H1; rewrite H1; apply refl_equal.
rewrite <- IH in H1; rewrite H1; apply Bool.orb_true_r.
destruct H as [l' H].
assert (K : exists sigma' : substitution,
  (forall x : variable, In x l' ->
   apply_subst sigma (Var symbol x) = apply_subst sigma' (Var symbol x)) /\
  (forall x : variable, In x l' <-> In x (map (@fst _ _) sigma'))).
clear l H; induction l' as [ | x l].
exists nil; split.
intros; contradiction.
simpl; intro x; split; exact (fun h => h).
destruct IHl as [sigma' [H1 H2]].
exists ((x, apply_subst sigma (Var _ x)) :: sigma'); split; simpl.
intros v [H | H].
subst v; rewrite (DType.eq_bool_refl X); apply refl_equal.
generalize (DType.eq_bool_ok X v x); case (DType.eq_bool X v x).
intro v_eq_x; subst x; apply refl_equal.
intros _; apply (H1 v H).
intro v; split; intros [H | H].
left; assumption.
right; rewrite <- H2; assumption.
left; assumption.
right; rewrite H2; assumption.
destruct K as [sigma' [H1 H2]]; exists sigma'; split.
intros x H3; rewrite H in H3; apply H1; assumption.
intros x; rewrite H; apply H2.
Qed.

Section FreshVar.

Hypothesis var_of_nat : nat -> variable.
Hypothesis nat_of_var : variable -> nat.
Hypothesis nat_of_var_of_nat : forall n, nat_of_var (var_of_nat n) = n. 

Function max_var_list (n : nat) (l : list term)  { measure (list_size (@size _ _)) l } : nat :=
  match l with
    | nil => n
    | (Var y) :: l => max_var_list (max n (nat_of_var y)) l
    | (Term _ ll) :: l => max (max_var_list n ll) (max_var_list n l)
end.
Proof.
intros _ l t l' y H1 H2;  simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; auto with arith.
intros _ l t l' f ll H1 H2; simpl; apply lt_le_trans with (size (Term f ll)).
simpl; auto with arith.
simpl; auto with arith.
Defined.

Lemma max_var_list_is_ub : 
  forall n l m, m = max_var_list n l -> (n <= m /\ forall x, var_in_term_list X x l = true -> nat_of_var x <= m).
Proof.
intros n l; apply max_var_list_ind; clear n l.
(* 1/3 *)
intros n l H m K; subst m; split; [apply le_n | intros; discriminate].
(* 1/2 *)
intros n xl x l H IH m K; split.
apply le_trans with (max n (nat_of_var x)); [apply le_max_l | apply (proj1 (IH _ K))].
intro v; rewrite var_in_term_list_unfold, Bool.orb_true_iff; intros [J | J].
simpl in J; assert (L := DType.eq_bool_ok X x v); rewrite J in L; subst v.
apply le_trans with  (max n (nat_of_var x)); [apply le_max_r | apply (proj1 (IH _ K))].
apply (proj2 (IH _ K) _ J).
(* 1/1 *)
intros n fkl f k l H IHk IHl m K; split.
apply le_trans with (max_var_list n k); [apply (proj1 (IHk _ (refl_equal _))) | rewrite K; apply le_max_l].
intro v; rewrite var_in_term_list_unfold, Bool.orb_true_iff; intros [J | J].
simpl in J; apply le_trans with (max_var_list n k); [ | rewrite K; apply le_max_l].
apply (proj2 (IHk _ (refl_equal _)) _ J).
apply le_trans with (max_var_list n l); [apply (proj2 (IHl _ (refl_equal _)) _ J) | rewrite K; apply le_max_r].
Qed.

Lemma max_var_list_is_lub : 
   forall n l m, n <= m -> (forall x, var_in_term_list X x l = true -> nat_of_var x <= m) -> max_var_list n l <= m.
Proof.
intros n l; revert n; pattern l.
apply (list_rec3 (@size symbol variable)); clear l.
fix 1; intro nl; case nl; clear nl.
- intros l; case l; clear l.
  + intros _ n m Hn _; apply Hn.
  + intros t l H n m Hn Hl.
    case_eq t; [intro y | intros f k]; intros Ht; subst t; simpl in H; inversion H.
- intros nl l; case l; clear l.
  + intros _ n m Hn _; apply Hn. 
  + intros t l H n m Hn Hl; rewrite max_var_list_equation.
    case_eq t; [intro y | intros f k]; intros Ht; subst t.
    * apply (max_var_list_is_lub nl).
      apply le_S_n; apply H.
      apply max_case; [assumption | ].
      apply Hl; rewrite var_in_term_list_unfold; simpl.
      rewrite DType.eq_bool_refl; apply refl_equal.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold, Hx, Bool.orb_true_r; apply refl_equal.
    * apply max_case; apply (max_var_list_is_lub nl).
      apply le_S_n; refine (le_trans _ _ _ _ H); simpl; apply le_n_S; apply le_plus_l.
      assumption.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold; simpl; rewrite Hx; apply refl_equal.
      apply le_S_n; refine (le_trans _ _ _ _ H); simpl; apply le_n_S; apply le_plus_r.
      assumption.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold, Hx, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma max_var_list_is_monotonic :
  forall l1 l2 n1 n2,
    (forall x, var_in_term_list X x l1 = true -> var_in_term_list X x l2 = true) ->
    n1 <= max_var_list n2 l2 ->
    max_var_list n1 l1 <= max_var_list n2 l2.
Proof.
intro l1; pattern l1.
apply (list_rec3 (@size symbol variable)); clear l1.
fix 1; intro nl; case nl; clear nl.
- intros l1; case l1; clear l1.
  + intros _ l2 n1 n2 _ Hn; rewrite max_var_list_equation; assumption.
  + intros t1 l1 H1.
    case_eq t1; [intro y | intros f k]; intros Ht1; subst t1; simpl in H1; inversion H1.
- intros nl l1; case l1; clear l1.
  + intros _ l2 n1 n2 _ Hn; rewrite max_var_list_equation; assumption.
  + intros t1 l1 H1 l2 n1 n2 Hl Hn; rewrite max_var_list_equation.
    case_eq t1; [intro y | intros f k]; intros Ht1; subst t1.
    * apply (max_var_list_is_monotonic nl).
      apply le_S_n; apply H1.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold, Hx, Bool.orb_true_r; apply refl_equal.
      apply max_case; [assumption | ].
      apply (proj2 (max_var_list_is_ub n2 l2 (refl_equal _))).
      apply Hl; rewrite var_in_term_list_unfold; simpl; rewrite DType.eq_bool_refl; apply refl_equal.
    * apply max_case; apply (max_var_list_is_monotonic nl).
      apply le_S_n; refine (le_trans _ _ _ _ H1); simpl; apply le_n_S; apply le_plus_l.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold; simpl; rewrite Hx; apply refl_equal.
      assumption.
      apply le_S_n; refine (le_trans _ _ _ _ H1); simpl; apply le_n_S; apply le_plus_r.
      intros x Hx; apply Hl; rewrite var_in_term_list_unfold, Hx, Bool.orb_true_r; apply refl_equal.
      assumption.
Qed.

Lemma Fresh_nat : 
  forall (l : list term) n, var_in_term_list X (var_of_nat (S (max_var_list n l))) l = false.
Proof.
intros l n; case_eq (var_in_term_list X (var_of_nat (S (max_var_list n l))) l); intro Kl; [ | apply refl_equal].
assert (Hl := proj2 (max_var_list_is_ub n l (refl_equal _)) (var_of_nat (S (max_var_list n l))) Kl).
rewrite nat_of_var_of_nat in Hl; apply False_rec.
apply (lt_irrefl _ Hl).
Qed.

Lemma incr_subst :
  forall (k l : list term) sigma, exists lv, exists sigma',
  map (apply_subst sigma) l = map (apply_subst (sigma' ++ sigma)) l /\
  k = map (apply_subst (sigma' ++ sigma)) (map (@Var _ _ _) lv).
Proof.
intro k; induction k as [ | t k]; intros l sigma.
exists nil; exists nil; split; apply refl_equal.
destruct (IHk l sigma) as [lv [sigma' [Hl Hk]]].
assert (F1 := Fresh_nat (l ++ (map (@Var _ _ _) lv)) 0).
set (v1 := var_of_nat (S (max_var_list 0 (l ++ map (@Var _ symbol _) lv)))) in *; clearbody v1.
exists (v1 :: lv); exists ((v1, t) :: sigma'); split.
rewrite Hl; rewrite <- map_eq.
intros a a_in_l.
rewrite <- subst_eq_vars.
intros v v_in_a; simpl.
generalize (DType.eq_bool_ok X v v1); case (DType.eq_bool X v v1); [intro v_eq_v1; subst v1 | intros _; apply refl_equal].
destruct (In_split _ _ a_in_l) as [l1 [l2 H]]; rewrite H in F1.
do 2 rewrite var_in_term_list_app in F1.
rewrite var_in_term_list_unfold, v_in_a, Bool.orb_true_r in F1; discriminate.
simpl; rewrite (DType.eq_bool_refl X); apply f_equal.
rewrite Hk; rewrite <- map_eq; intros a a_in_lv; rewrite <- subst_eq_vars.
intros v v_in_a; simpl.
generalize (DType.eq_bool_ok X v v1); case (DType.eq_bool X v v1); [intro v_eq_v1; subst v1 | intros _; apply refl_equal].
destruct (In_split _ _ a_in_lv) as [lv1 [lv2 H]]; rewrite H in F1.
do 2 rewrite var_in_term_list_app in F1.
rewrite var_in_term_list_unfold, v_in_a in F1.
do 2 rewrite Bool.orb_true_r in F1; discriminate.
Qed.

End FreshVar.
*)
End Sec.

