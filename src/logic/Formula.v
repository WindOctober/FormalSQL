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
Require Import BasicFacts ListFacts Bool3 OrderedSet Term Tree FiniteSet ListPermut ListSort.

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

Section Sec.

Hypothesis dom : Type.
Hypothesis predicate : Type.
Hypothesis symbol : Type.

Notation variable := (variable dom).

Notation term := (term dom symbol).

Inductive formula : Type :=
  | TTrue : formula
  | Atom : predicate -> list term -> formula
  | Conj : and_or -> formula -> formula -> formula
  | Not : formula -> formula 
  | Quant : quantifier -> variable -> formula -> formula.

(* begin hide *)

Inductive All_F : Type :=
  | All_F_dom : dom -> All_F
  | All_F_N : N -> All_F
  | All_F_predicate : predicate -> All_F
  | All_F_symbol : symbol -> All_F.

Open Scope N_scope.

Definition N_of_All_F (a : All_F) : N :=
  match a with
  | All_F_dom _ => 0
  | All_F_N _ => 1
  | All_F_predicate _ => 2
  | All_F_symbol _ => 3
  end.

Definition all_f_compare dom_compare predicate_compare symbol_compare a1 a2 :=
   match N.compare (N_of_All_F a1) (N_of_All_F a2) with
   | Lt => Lt
   | Gt => Gt
   | Eq =>
     match a1, a2 with
       | All_F_dom s1, All_F_dom s2 => dom_compare s1 s2
       | All_F_N n1, All_F_N n2 => Oset.compare ON n1 n2
       | All_F_predicate p1, All_F_predicate p2 => predicate_compare p1 p2
       | All_F_symbol s1, All_F_symbol s2 => symbol_compare s1 s2
       | _, _ => Eq
     end
   end.

Section Compare.

Hypothesis ODom : Oset.Rcd dom.
Hypothesis OP : Oset.Rcd predicate.
Hypothesis OSymb : Oset.Rcd symbol.

Definition OAll_F : Oset.Rcd All_F.
split with (all_f_compare (Oset.compare ODom) (Oset.compare OP) (Oset.compare OSymb)); 
            unfold all_f_compare.
(* 1/3 *)
- intros a1 a2.
  case a1; clear a1;
  (intro x1; case a2; clear a2; try discriminate; intro x2; simpl).
  + generalize (Oset.eq_bool_ok ODom x1 x2);
    case (Oset.compare ODom x1 x2).
    * apply f_equal.
    * intros H AH; injection AH; apply H.
    * intros H AH; injection AH; apply H.
  + generalize (Oset.eq_bool_ok ON x1 x2); simpl;
    case (N.compare x1 x2).
    * apply f_equal.
    * intros H AH; injection AH; apply H.
    * intros H AH; injection AH; apply H.
  + generalize (Oset.eq_bool_ok OP x1 x2);
    case (Oset.compare OP x1 x2).
    * apply f_equal.
    * intros H AH; injection AH; apply H.
    * intros H AH; injection AH; apply H.
  + generalize (Oset.eq_bool_ok OSymb x1 x2);
    case (Oset.compare OSymb x1 x2).
    * apply f_equal.
    * intros H AH; injection AH; apply H.
    * intros H AH; injection AH; apply H.
- (* 2/3 *)
  intros a1 a2 a3.
  case a1; clear a1; 
  (intro x1; case a2; clear a2; try discriminate; 
   (intro x2; case a3; clear a3; intro x3; simpl; 
    try (trivial || discriminate || apply (Oset.compare_lt_trans _ x1 x2 x3)))).
  apply (Oset.compare_lt_trans ON x1 x2 x3).
- (* 3/3 *)
  intros a1 a2.
  case a1; clear a1; 
  (intro x1; case a2; clear a2; intro x2; simpl; 
   try (trivial || discriminate || apply (Oset.compare_lt_gt _ x1 x2))).
  apply (Oset.compare_lt_gt ON).
Defined.

Definition tree_of_dom (s : dom) : tree All_F := 
  Node 1 (Leaf (All_F_dom s) :: nil).

Definition tree_of_var (v : variable) : tree All_F :=
    match v with
  | Vrbl s n => Node 2 ((tree_of_dom s) :: (Leaf (All_F_N n)) :: nil)
  end.

Fixpoint tree_of_term (t : term) : tree All_F :=
  match t with
    | Var v => Node 3 (tree_of_var v :: nil)
    | Term f l => Node 4 (Leaf (All_F_symbol f) :: (List.map tree_of_term l))
  end.

Fixpoint tree_of_formula (f : formula) : tree All_F :=
  match f with
 | TTrue => Node 6 (Leaf (All_F_N 0):: nil) 
 | Atom p l => Node 5 (Leaf (All_F_predicate p) :: (List.map tree_of_term l))
 | Conj c f1 g1 => 
     Node 
       (match c with And_F => 10 | Or_F => 11 end)
       ((tree_of_formula f1) :: (tree_of_formula g1) :: nil)
 | Not f1 => Node 12 ((tree_of_formula f1) :: nil)
 | Quant q x f1 => 
     Node 
       (match q with Forall_F => 13 | Exists_F => 14 end)
       ((tree_of_var x) :: (tree_of_formula f1) :: nil)
 end.

Close Scope N_scope.

Definition OVR : Oset.Rcd variable.
split with (fun v1 v2 => Oset.compare (OTree OAll_F) (tree_of_var v1) (tree_of_var v2)).
- intros a1 a2.
  generalize (Oset.eq_bool_ok (OTree OAll_F) (tree_of_var a1) (tree_of_var a2)).
  case (Oset.compare (OTree OAll_F) (tree_of_var a1) (tree_of_var a2)).
  + destruct a1 as [d1 v1]; destruct a2 as [d2 v2]; simpl.
    intro H; injection H; clear H.
    do 2 intro; apply f_equal2; assumption.
  + intros H K; apply H; apply f_equal; assumption.
  + intros H K; apply H; apply f_equal; assumption.
- do 3 intro; apply Oset.compare_lt_trans.
- do 2 intro; apply Oset.compare_lt_gt.
Defined.

Definition FVR := Fset.build OVR.

(* end hide *)

Section Var.

(** Variables occurring in terms, atoms and formulae. *)

Fixpoint free_variables_f (f : formula) :=
  match f with
  | TTrue => Fset.empty FVR
  | Atom _ l => Fset.Union _ (List.map (variables_t FVR) l)
  | Conj _ f1 f2  => (free_variables_f f1) unionS (free_variables_f f2)
  | Not f1 => free_variables_f f1
  | Quant _ x f1 =>
     Fset.filter FVR (fun y => negb (Oset.eq_bool OVR x y)) (free_variables_f f1)
  end.

Lemma free_variables_f_unfold :
  forall f, free_variables_f f = 
            match f with
              | TTrue => Fset.empty FVR
              | Atom _ l => Fset.Union _ (List.map (variables_t FVR) l)
              | Conj _ f1 f2 => (free_variables_f f1) unionS (free_variables_f f2)
              | Not f1 => free_variables_f f1
              | Quant _ x f1 =>
                Fset.filter FVR (fun y => negb (Oset.eq_bool OVR x y)) (free_variables_f f1)
            end.
Proof.
intro f; case f; intros; apply refl_equal.
Qed.

Fixpoint variables_f (f : formula) :=
  match f with
  | TTrue => Fset.empty FVR
  | Atom _ l => Fset.Union _ (List.map (variables_t FVR) l)
  | Conj _ f1 f2  => (variables_f f1) unionS (variables_f f2)
  | Not f1 => variables_f f1
  | Quant _ x f1 => Fset.add _ x (variables_f f1)
  end.

Lemma variables_f_unfold :
  forall f, variables_f f = 
            match f with
              | TTrue => Fset.empty FVR
              | Atom _ l =>  Fset.Union _ (List.map (variables_t FVR) l)
              | Conj _ f1 f2  => (variables_f f1) unionS (variables_f f2)
              | Not f1 => variables_f f1
              | Quant _ x f1 => Fset.add _ x (variables_f f1)
  end.
Proof.
intro f; case f; intros; apply refl_equal.
Qed.

Lemma in_variables_t_size :
  forall x t, x inS variables_t FVR t -> tree_size (tree_of_var x) < tree_size (tree_of_term t).
Proof.
intros x t; pattern t; apply term_rec3; clear t.
- intros v H; rewrite variables_t_unfold in H.
  rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in H.
  subst v; simpl.
  rewrite plus_n_O; apply le_n.
- intros f l IH H; rewrite variables_t_unfold in H.
  rewrite Fset.mem_Union in H.
  destruct H as [s [Hs H]].
  rewrite in_map_iff in Hs.
  destruct Hs as [t [Ht Hs]]; subst s.
  refine (Le.le_trans _ _ _ (IH t Hs H) _).
  simpl; do 2 apply le_S.
  apply in_list_size; rewrite in_map_iff.
  exists t; split; trivial.
Qed.

Lemma in_variables_f_size :
  forall x f, x inS variables_f f -> tree_size (tree_of_var x) <= tree_size (tree_of_formula f).
Proof.
intros x f H; induction f; rewrite variables_f_unfold in H.
- rewrite Fset.empty_spec in H; discriminate H.
- rewrite Fset.mem_Union in H.
  destruct H as [s [Hs H]].
  rewrite in_map_iff in Hs.
  destruct Hs as [t [Ht Hs]]; subst s.
  apply le_S_n; refine (Le.le_trans _ _ _ (in_variables_t_size x t H) _).
  apply Lt.lt_le_weak; apply Le.le_n_S; simpl.
  do 2 apply le_S; apply in_list_size; rewrite in_map_iff; exists t; split; trivial.
- simpl; apply le_S.
  rewrite Fset.mem_union, Bool.Bool.orb_true_iff in H.
  destruct H as [H | H].
  + refine (Le.le_trans _ _ _ (IHf1 H) _).
    apply le_plus_l.
  + refine (Le.le_trans _ _ _ (IHf2 H) _).
    rewrite <- (plus_n_O (tree_size (tree_of_formula f2))) at 1; apply le_plus_r.
- simpl; apply le_S.
  repeat rewrite plus_n_O; apply (IHf H).
- simpl; apply le_S.
  rewrite Fset.add_spec, Bool.Bool.orb_true_iff in H.
  destruct H as [H | H].
  + rewrite Oset.eq_bool_true_iff in H; subst v.
    apply le_plus_l.
  + refine (Le.le_trans _ _ _ (IHf H) _).
    rewrite <- (plus_n_O (tree_size (tree_of_formula f))) at 1; apply le_plus_r.
Qed.

Lemma free_variables_f_variables_f :
  forall f, free_variables_f f subS variables_f f.
Proof.
intro f; rewrite Fset.subset_spec; induction f; 
rewrite free_variables_f_unfold, variables_f_unfold; trivial.
- intro x; rewrite 2 Fset.mem_union, 2 Bool.Bool.orb_true_iff.
  intros [H | H]; [left; apply IHf1 | right; apply IHf2]; assumption.
- intros x Hx; rewrite Fset.mem_filter, Bool.Bool.andb_true_iff in Hx.
  rewrite Fset.add_spec, (IHf _ (proj1 Hx)), Bool.orb_true_r.
  apply refl_equal.
Qed.

End Var.

Section Interp.

Hypothesis B : Bool.Rcd.
Hypothesis value : Type.
Hypothesis OVal : Oeset.Rcd value.
Hypothesis base_value : Type.
Hypothesis interp_pred : predicate -> list base_value -> Bool.b B.
Hypothesis interp_term : (variable -> value) -> term -> base_value.
Hypothesis default_value : dom -> value.

Notation "s1 '=PE=' s2" := 
  (_permut  (fun x y => Oeset.compare OVal x y = Eq) s1 s2) (at level 70, no associativity).
Notation "a 'inE' s" := (Oeset.mem_bool OVal a s = true) (at level 70, no associativity).

Definition interp_conj a := 
  match a with 
    | And_F => Bool.andb B
    | Or_F => Bool.orb B
  end.

Definition interp_quant qf :=
  match qf with
      Forall_F => Bool.forallb B
    | Exists_F => Bool.existsb B
  end.

Definition empty_ivar : variable -> value :=
  fun x => match x with Vrbl s _ => default_value s end.

(** [ivar_xt ivar x t] is a valuation which behaves as [ivar], except on [x], which is interpreted as [t]. *)
Definition ivar_xt (ivar : variable -> value) (x : variable) (v : value) :=
  (fun y => match Oset.compare OVR x y with Eq => v | _ => ivar y end).

Lemma interp_quant_eq :
  forall q i1 i2 s1 s2, 
    s1 =PE= s2 -> 
    (forall x1 x2, x1 inE s1 -> Oeset.compare OVal x1 x2 = Eq -> i1 x1 = i2 x2) ->
    interp_quant q i1 s1 = interp_quant q i2 s2.
Proof.
intros q i1 i2 s1 s2 Hs Hi; unfold interp_quant; destruct q.
- apply (Bool.forallb_eq _ OVal); trivial.
- apply (Bool.existsb_eq _ OVal); trivial.
Qed.

Hypothesis interp_term_eq_rec :
  forall i1 i2 v x1 x2 s,
    Oeset.compare OVal x1 x2 = Eq ->
    (forall t, variables_t FVR t subS 
                           Fset.filter FVR
                           (fun y : variable => negb (Oset.eq_bool OVR v y)) s ->
               interp_term i1 t = interp_term i2 t) ->
    forall t, variables_t FVR t subS s -> 
              interp_term (ivar_xt i1 v x1) t = interp_term (ivar_xt i2 v x2) t.

Section Sec.
(** [I] is an "instance", that is a function which associates a set of values to each [dom]. *)
Hypothesis I : dom -> list value.

Fixpoint interp_formula ivar (f : formula) : Bool.b B :=
  match f with
  | TTrue => Bool.true _
  | Atom p l => interp_pred p (List.map (interp_term ivar) l)
  | Conj a f1 f2 => 
    (interp_conj a)
      (interp_formula ivar f1) (interp_formula ivar f2)
  | Not f1 => Bool.negb _ (interp_formula ivar f1)
  | Quant q (Vrbl d1 n1 as x1) f1 =>
    (** the domain [d1] occuring inside variable [x1] = [Vrbl d1 n1] indicates the scope of the universal quantifier. *)
    (interp_quant q) _
      (fun t => interp_formula (ivar_xt ivar x1 t) f1) 
       (I d1)
  end.

Lemma interp_formula_unfold :
  forall ivar f, interp_formula ivar f =
  match f with
  | TTrue => Bool.true _
  | Atom p l => interp_pred p (List.map (interp_term ivar) l)
  | Conj a f1 f2 => 
    (interp_conj a)
      (interp_formula ivar f1) (interp_formula ivar f2)
  | Not f1 => Bool.negb _ (interp_formula ivar f1)
  | Quant q (Vrbl d1 n1 as x1) f1 =>
    (interp_quant q) _
      (fun t => interp_formula (ivar_xt ivar x1 t) f1) 
       (I d1)
  end.
Proof.
intros ivar f; case f; intros; apply refl_equal.
Qed.

Lemma interp_formula_eq :
  forall f i1 i2,
    (forall t, Fset.subset _ (variables_t FVR t) (free_variables_f f) = true -> 
               interp_term i1 t = interp_term i2 t) ->
    interp_formula i1 f = interp_formula i2 f.
Proof.
intro f; induction f; intros i1 i2 Hi; simpl.
- apply refl_equal.
- apply f_equal; rewrite <- map_eq.
  intros t Ht; apply Hi.
  simpl free_variables_f.
  rewrite Fset.subset_spec; intros x Hx.
  rewrite Fset.mem_Union.
  exists (variables_t FVR t); split; [ | assumption].
  rewrite in_map_iff; exists t; split; trivial.
- apply f_equal2.
  + apply IHf1.
    intros t Ht; apply Hi.
    rewrite Fset.subset_spec in Ht.
    rewrite Fset.subset_spec; intros x Hx.
    rewrite free_variables_f_unfold, Fset.mem_union.
    rewrite (Ht _ Hx).
    apply refl_equal.
  + apply IHf2.
    intros t Ht; apply Hi.
    rewrite Fset.subset_spec in Ht.
    rewrite Fset.subset_spec; intros x Hx.
    rewrite free_variables_f_unfold, Fset.mem_union.
    rewrite (Ht _ Hx), Bool.orb_true_r.
    apply refl_equal.
- apply f_equal; apply IHf; apply Hi.
- destruct v as [dv nv].
  case q; unfold interp_quant.
  + apply (Bool.forallb_eq _ OVal).
    * apply Oeset.permut_refl.
    * intros; apply IHf.
      intros t Ht.
      revert Ht; apply interp_term_eq_rec; trivial.
  + apply (Bool.existsb_eq _ OVal).
    * apply Oeset.permut_refl.
    * intros; apply IHf.
      intros t Ht.
      revert Ht; apply interp_term_eq_rec; trivial.
Qed.

End Sec.

Hypothesis interp_term_eq :
  forall i1 i2 t, 
    (forall x, x inS variables_t FVR t -> Oeset.compare OVal (i1 x) (i2 x) = Eq) -> 
    interp_term i1 t = interp_term i2 t.

Lemma interp_formula_interp_dom_eq : 
  forall f I1 I2 i, (forall d n, Vrbl d n inS (variables_f f) -> I1 d =PE= I2 d) -> 
                    interp_formula I1 i f = interp_formula I2 i f. 
Proof.
intro f; induction f; intros I1 I2 i H; trivial.
- simpl; apply f_equal2; [apply IHf1 | apply IHf2]; 
  intros d m K; apply (H d m);
  rewrite variables_f_unfold, Fset.mem_union, Bool.Bool.orb_true_iff;
  [left | right]; assumption.
- simpl; apply f_equal; apply IHf; assumption.
- rewrite 2 (interp_formula_unfold _ _ (Quant _ _ _)).
  destruct v as [d1 v1].
  assert (Hd1 : I1 d1 =PE= I2 d1).
  {
    apply (H d1 v1).
    rewrite variables_f_unfold, Fset.add_spec, Bool.Bool.orb_true_iff; left.
    rewrite Oset.eq_bool_true_iff; apply refl_equal.
  }
  destruct q; unfold interp_quant.
  + apply (Bool.forallb_eq B OVal); [assumption | ].
    intros x1 x2 Hx1 Hx.
    refine (eq_trans (IHf I1 I2 _ _) _).
    * intros d n J; apply (H d n).
      rewrite variables_f_unfold, Fset.add_spec, Bool.Bool.orb_true_iff; right; assumption.
    * apply interp_formula_eq; intros t _; apply interp_term_eq.
      intros y Hy; unfold ivar_xt.
      case (Oset.compare OVR (Vrbl d1 v1) y); [assumption | | ]; apply Oeset.compare_eq_refl.
  + apply (Bool.existsb_eq B OVal); [assumption | ].
    intros x1 x2 Hx1 Hx.
    refine (eq_trans (IHf I1 I2 _ _) _).
    * intros d n J; apply (H d n).
      rewrite variables_f_unfold, Fset.add_spec, Bool.Bool.orb_true_iff; right; assumption.
    * apply interp_formula_eq; intros t _; apply interp_term_eq.
      intros y Hy; unfold ivar_xt.
      case (Oset.compare OVR (Vrbl d1 v1) y); [assumption | | ]; apply Oeset.compare_eq_refl.
Qed.

Lemma quant_swapp :
  forall qtf x1 x2 f I i, interp_formula I i (Quant qtf x1 (Quant qtf x2 f)) = 
                    interp_formula I i (Quant qtf x2 (Quant qtf x1 f)).
Proof.
intros qtf [d1 v1] [d2 v2] f I i.
case_eq (Oset.eq_bool OVR (Vrbl d1 v1) (Vrbl d2 v2)).
- rewrite Oset.eq_bool_true_iff; intro H; rewrite H; apply refl_equal.
- intro Hv.
  set (i1 t2 t1 := (ivar_xt (ivar_xt i (Vrbl d1 v1) t1) (Vrbl d2 v2) t2)).
  set (i2 t2 t1 := (ivar_xt (ivar_xt i (Vrbl d2 v2) t2) (Vrbl d1 v1) t1)).
  apply trans_eq with
      (interp_quant qtf
                    (fun t1 : value =>
                       interp_quant qtf
                                    (fun t2 : value => interp_formula I (i1 t2 t1) f)
                                    (I d2)) (I d1)); [unfold i1; apply refl_equal | ].
  apply trans_eq  with
      (interp_quant qtf
                    (fun t2 : value =>
                       interp_quant qtf
                                    (fun t1 : value => interp_formula I (i2 t2 t1) f)
                                    (I d1)) (I d2)); [ | unfold i2; apply refl_equal].
  set (l1 := I d1) in *; clearbody l1.
  set (l2 := I d2) in *; clearbody l2.
  destruct qtf; unfold interp_quant; simpl.
  + induction l1 as [ | x1 l1].
    * simpl; induction l2 as [ | x2 l2]; simpl; [apply refl_equal | ].
      rewrite Bool.andb_true_l, <- IHl2; apply refl_equal.
    * rewrite (Bool.forallb_forallb_unfold B OVal), Bool.forallb_unfold, IHl1.
      apply f_equal2; [ | apply refl_equal].
      clear l1 IHl1; induction l2 as [ | x2 l2]; [apply refl_equal | ].
      rewrite 2 (Bool.forallb_unfold B _ (_ :: _)).
      apply f_equal2; [ | apply IHl2].
      unfold i1, i2.
      apply interp_formula_eq; intros t Ht.
      apply interp_term_eq; intros x Hx.
      unfold ivar_xt.
      {
        case_eq (Oset.compare OVR (Vrbl d2 v2) x).
        - rewrite Oset.compare_eq_iff; intro; subst x.
          case_eq (Oset.compare OVR (Vrbl d1 v1) (Vrbl d2 v2)); intro Kv.
          + unfold Oset.eq_bool in Hv; rewrite Kv in Hv; discriminate Hv.
          + apply Oeset.compare_eq_refl.
          + apply Oeset.compare_eq_refl.
        - intros _; apply Oeset.compare_eq_refl.
        - intros _; apply Oeset.compare_eq_refl.
      }
  + induction l1 as [ | x1 l1].
    * simpl; induction l2 as [ | x2 l2]; simpl; [apply refl_equal | ].
      rewrite Bool.orb_false_l, <- IHl2; apply refl_equal.
    * rewrite (Bool.existsb_existsb_unfold B OVal), Bool.existsb_unfold, IHl1.
      apply f_equal2; [ | apply refl_equal].
      clear l1 IHl1; induction l2 as [ | x2 l2]; [apply refl_equal | ].
      rewrite 2 (Bool.existsb_unfold B _ (_ :: _)).
      apply f_equal2; [ | apply IHl2].
      unfold i1, i2.
      apply interp_formula_eq; intros t Ht.
      apply interp_term_eq; intros x Hx.
      unfold ivar_xt.
      {
        case_eq (Oset.compare OVR (Vrbl d2 v2) x).
        - rewrite Oset.compare_eq_iff; intro; subst x.
          case_eq (Oset.compare OVR (Vrbl d1 v1) (Vrbl d2 v2)); intro Kv.
          + unfold Oset.eq_bool in Hv; rewrite Kv in Hv; discriminate Hv.
          + apply Oeset.compare_eq_refl.
          + apply Oeset.compare_eq_refl.
        - intros _; apply Oeset.compare_eq_refl.
        - intros _; apply Oeset.compare_eq_refl.
      }
Qed.

Fixpoint quant_list qtf l f :=
  match l with
    | nil => f
    | x :: lx => Quant qtf x (quant_list qtf lx f)
  end.

Lemma quant_list_unfold :
  forall qtf l f, quant_list qtf l f =   
              match l with
                | nil => f
                | x :: lx => Quant qtf x (quant_list qtf lx f)
              end.
Proof.
intros qtf l f; case l; intros; apply refl_equal.
Qed.

Lemma free_variables_f_quant_list :
  forall qtf l f, free_variables_f (quant_list qtf l f) =S= 
                  Fset.diff _ (free_variables_f f) (Fset.mk_set _ l).
Proof.
intros qtf l f; rewrite Fset.equal_spec; intro x;
induction l as [ | x1 l]; rewrite quant_list_unfold.
- rewrite Fset.mem_diff, Fset.empty_spec, Bool.andb_true_r.
  apply refl_equal.
- rewrite Fset.mem_diff, free_variables_f_unfold, Fset.mem_filter, IHl.
  rewrite Fset.mem_diff, 2 Fset.mem_mk_set, (Oset.mem_bool_unfold _ _ (_ :: _)).
  rewrite <- Bool.Bool.andb_assoc; apply f_equal.
  rewrite Bool.Bool.negb_orb, Bool.Bool.andb_comm; apply f_equal2; [ | apply refl_equal].
  rewrite Oset.compare_lt_gt; unfold Oset.eq_bool.
  destruct (Oset.compare OVR x1 x); trivial.
Qed.

Lemma quant_list_app :
  forall qtf l1 l2 f I i,
    interp_formula I i (quant_list qtf l1 (quant_list qtf l2 f)) =
    interp_formula I i (quant_list qtf (l1 ++ l2) f).
Proof.
intros qtf l1; induction l1 as [ | [d1 n1] l1]; intros l2 f I i; simpl; [apply refl_equal | ].
apply interp_quant_eq.
- apply Oeset.permut_refl.
- intros x1 x2 Hx1 Hx; rewrite IHl1.
  apply interp_formula_eq; intros; apply interp_term_eq.
  intros; unfold ivar_xt.
  case (Oset.compare OVR (Vrbl d1 n1) x); trivial; apply Oeset.compare_eq_refl.
Qed.

Lemma quant_list_Pcons_true :
  forall qtf l1 x l2 f I i, interp_formula I i (quant_list qtf (x :: l1 ++ l2) f) =
                       interp_formula I i (quant_list qtf (l1 ++ x :: l2) f).
Proof.
intros qtf l1; induction l1 as [ | [d1 n1] l1]; intros [d n] l2 f I i; [apply refl_equal | ].
assert (K := quant_swapp qtf (Vrbl d n) (Vrbl d1 n1) (quant_list qtf (l1 ++ l2) f) I i).
simpl app.
rewrite 3 (quant_list_unfold _ (_ :: _)), K.
simpl; apply interp_quant_eq; [apply Oeset.permut_refl | ].
intros x1 x2 Hx1 Hx.
assert (IH := IHl1 (Vrbl d n) l2 f I (ivar_xt i (Vrbl d1 n1) x1)).
simpl in IH; rewrite IH.
apply interp_formula_eq; intros; apply interp_term_eq.
intros x Kx; unfold ivar_xt.
case (Oset.compare OVR (Vrbl d1 n1) x); trivial; apply Oeset.compare_eq_refl.
Qed.

Lemma quant_list_permut_true :
  forall qtf l1 l2 f I i, _permut (@eq _) l1 l2 -> 
                      interp_formula I i (quant_list qtf l1 f) = 
                      interp_formula I i (quant_list qtf l2 f).
Proof.
intros qtf l1; induction l1 as [ | x1 l1]; intros l2 f I i H; inversion H; clear H; subst; 
[apply refl_equal | ].
rewrite <- quant_list_Pcons_true.
simpl; destruct b as [d1 n1].
apply interp_quant_eq.
- apply Oeset.permut_refl.
- intros x1 x2 Hx1 Hx.
  rewrite (IHl1 _ f I (ivar_xt i (Vrbl d1 n1) x1) H4).
  apply interp_formula_eq; intros; apply interp_term_eq.
  intros x Kx; unfold ivar_xt.
  case (Oset.compare OVR (Vrbl d1 n1) x); trivial; apply Oeset.compare_eq_refl.
Qed.

Lemma quant_forall_list_true_iff :
  forall lx f I i, all_diff lx  ->
     (interp_formula I i (quant_list Forall_F lx f) = Bool.true B <->
    (forall ii, (forall d n, In (Vrbl d n) lx -> In (ii (Vrbl d n)) (I d)) ->
                interp_formula 
                  I (fun x => if Oset.mem_bool OVR x lx then ii x else i x) f = Bool.true B)).
Proof.
intro lx; induction lx as [ | [d1 n1] lx]; intros f I i Hlx; simpl; split.
- exact (fun h _ _ => h).
- intro H; apply (H i); intros; contradiction.
- rewrite Bool.forallb_forall_true; intros H ii Hii.
  rewrite all_diff_unfold in Hlx; destruct Hlx as [H1 Hlx].
  assert (H' := H _ (Hii _ _ (or_introl _ (refl_equal _)))).
  rewrite (IHlx f I (ivar_xt i (Vrbl d1 n1) (ii (Vrbl d1 n1)))) in H';
    [ | intros; apply Hlx; right; assumption].
  rewrite <- (H' ii).
  + apply interp_formula_eq; intros t Ht.
    apply interp_term_eq; intros x Hx.
    case_eq (Oset.mem_bool OVR x lx); intro Kx.
    * rewrite Bool.orb_true_r; apply Oeset.compare_eq_refl.
    * rewrite Bool.orb_false_r; unfold ivar_xt, Oset.eq_bool.
      rewrite Oset.compare_lt_gt.
      case_eq (Oset.compare OVR (Vrbl d1 n1) x); intro Jx; 
      try (simpl; apply Oeset.compare_eq_refl).
      rewrite Oset.compare_eq_iff in Jx; subst x.
      apply Oeset.compare_eq_refl.
  + intros d n Hn; apply Hii; right; assumption.
- intro H; rewrite Bool.forallb_forall_true; intros v Hv.
  rewrite all_diff_unfold in Hlx.
  destruct Hlx as [H1 Hlx].
  rewrite (IHlx f I (ivar_xt i (Vrbl d1 n1) v)); [ | assumption].
  intros ii Hii.
  rewrite <- (H (ivar_xt ii (Vrbl d1 n1) v)).
  + apply interp_formula_eq; intros t Ht.
    apply interp_term_eq; intros x Hx; unfold ivar_xt.
    case_eq (Oset.mem_bool OVR x lx); intro Kx.
    * rewrite Bool.orb_true_r.
      case_eq (Oset.compare OVR (Vrbl d1 n1) x); intro Jx;
      try apply Oeset.compare_eq_refl.
      rewrite Oset.compare_eq_iff in Jx; subst x.
      apply False_rec; refine (H1 _ _ (refl_equal _)).
      rewrite <- (Oset.mem_bool_true_iff OVR); apply Kx.
    * rewrite Bool.orb_false_r; unfold Oset.eq_bool.
      rewrite (Oset.compare_lt_gt OVR x).
      case_eq (Oset.compare OVR (Vrbl d1 n1) x); intro Jx; 
      try (simpl; apply Oeset.compare_eq_refl).
  + intros d n Hx.
    unfold ivar_xt.
    case_eq (Oset.compare OVR (Vrbl d1 n1) (Vrbl d n)); intro Kx.
    * rewrite Oset.compare_eq_iff in Kx.
      injection Kx; clear Kx; intros; subst d n; assumption.
    * destruct Hx as [Hx | Hx]; [rewrite Hx, Oset.compare_eq_refl in Kx; discriminate Kx | ].
      apply Hii; assumption.
    * destruct Hx as [Hx | Hx]; [rewrite Hx, Oset.compare_eq_refl in Kx; discriminate Kx | ].
      apply Hii; assumption.
Qed.

Lemma quant_forall_set_true_iff :
  forall sx f I i, 
     (interp_formula I i (quant_list Forall_F (Fset.elements FVR sx) f) = Bool.true B <->
    (forall ii, (forall d n, In (Vrbl d n) (Fset.elements _ sx) -> In (ii (Vrbl d n)) (I d)) ->
                interp_formula 
                  I (fun x => if Oset.mem_bool OVR x (Fset.elements _ sx) 
                              then ii x 
                              else i x) f = Bool.true B)).
Proof.
intros sx f I i; apply quant_forall_list_true_iff.
apply Fset.all_diff_elements.
Qed.

Lemma quant_exists_list_true_iff :
  forall lx f I i, 
    all_diff lx ->
    (interp_formula I i (quant_list Exists_F lx f) = Bool.true B <->
    (exists ii, (forall d n, In (Vrbl d n) lx -> In (ii (Vrbl d n)) (I d)) /\
                interp_formula 
                  I (fun x => if Oset.mem_bool OVR x lx then ii x else i x) f = Bool.true B)).
Proof.
intro lx; induction lx as [ | [d1 n1] lx]; intros f I i Hlx; split.
- intro H; exists i; split; trivial.
  intros; contradiction.
- intros [ii [Hii H]]; apply H.
- rewrite all_diff_unfold in Hlx.
  destruct Hlx as [H1 Hlx]; simpl;
  rewrite Bool.existsb_exists_true; intros [v [Hv H]].
  rewrite IHlx in H.
  destruct H as [ii [Hii H]].
  exists (ivar_xt ii (Vrbl d1 n1) v); split.
  + unfold ivar_xt; intros d n Hn.
    case_eq (Oset.compare OVR (Vrbl d1 n1) (Vrbl d n)); intro Kx.
    * rewrite Oset.compare_eq_iff in Kx; injection Kx; clear Kx; do 2 intro; subst d1 n1.
      assumption.
    * apply Hii; destruct Hn as [Hn | Hn]; [ | assumption].
      injection Hn; clear Hn; do 2 intro; subst d1 n1; rewrite Oset.compare_eq_refl in Kx;
      discriminate Kx.
    * apply Hii; destruct Hn as [Hn | Hn]; [ | assumption].
      injection Hn; clear Hn; do 2 intro; subst d1 n1; rewrite Oset.compare_eq_refl in Kx;
      discriminate Kx.
  + rewrite <- H. 
    apply interp_formula_eq; intros t Ht.
    apply interp_term_eq; intros x Hx.
    unfold ivar_xt, Oset.eq_bool.
    rewrite Oset.compare_lt_gt.
    case_eq (Oset.compare OVR (Vrbl d1 n1) x); intro Kx; 
    try (simpl; apply Oeset.compare_eq_refl).
    rewrite Oset.compare_eq_iff in Kx; subst x; simpl.
    rewrite Oeset.compare_eq_refl_alt; [apply refl_equal | ].
    rewrite if_eq_false; [apply refl_equal | ].
    case_eq (Oset.mem_bool OVR (Vrbl d1 n1) lx); intro Kx; [ | apply refl_equal].
    apply False_rec; refine (H1 _ _ (refl_equal _)). 
    rewrite Oset.mem_bool_true_iff in Kx; apply Kx.
  + assumption.
- rewrite all_diff_unfold in Hlx.
  destruct Hlx as [H1 Hlx]; simpl; intros [ii [Hii H]].
  rewrite Bool.existsb_exists_true.
  exists (ii (Vrbl d1 n1)); split; [apply Hii; left; apply refl_equal | ].
  rewrite IHlx; [ | assumption].
  exists ii; split; [intros; apply Hii; right; assumption | ].
  rewrite <- H.
  apply interp_formula_eq; intros t Ht.
  apply interp_term_eq; intros x Hx; unfold ivar_xt.
  case_eq (Oset.mem_bool OVR x lx); intro Kx.
  + rewrite Bool.orb_true_r; apply Oeset.compare_eq_refl.
  + rewrite Bool.orb_false_r; unfold Oset.eq_bool.
    rewrite (Oset.compare_lt_gt _ x);
      case_eq (Oset.compare OVR (Vrbl d1 n1) x); intro Jx;
      try apply Oeset.compare_eq_refl.
      rewrite Oset.compare_eq_iff in Jx; subst x; simpl.
      apply Oeset.compare_eq_refl.
Qed.

Lemma quant_exists_set_true_iff :
  forall sx f I i, 
    (interp_formula I i (quant_list Exists_F (Fset.elements FVR sx) f) = Bool.true B <->
     (exists ii, (forall d n, In (Vrbl d n) (Fset.elements _ sx) -> In (ii (Vrbl d n)) (I d)) /\
                 interp_formula 
                   I (fun x => if Oset.mem_bool OVR x (Fset.elements _ sx) 
                               then ii x 
                               else i x) f = Bool.true B)).
Proof.
intros sx f I i; apply quant_exists_list_true_iff.
apply Fset.all_diff_elements.
Qed.

Lemma conj_swapp :
  forall a f1 f2 I i, interp_formula I i (Conj a f1 f2) = interp_formula I i (Conj a f2 f1).
Proof.
intros a f1 f2 I i; destruct a; simpl.
- apply Bool.andb_comm.
- apply Bool.orb_comm.
Qed.

Fixpoint conj_list a lf :=
  match lf with
    | nil => match a with And_F => TTrue | Or_F => Not TTrue end
    | f1 :: lf => Conj a f1 (conj_list a lf)
  end.

Lemma conj_list_unfold :
  forall a lf, conj_list a lf =
               match lf with
                 | nil => match a with And_F => TTrue | Or_F => Not TTrue end
                 | f1 :: lf => Conj a f1 (conj_list a lf)
               end.
Proof.
intros a lf; case lf; intros; apply refl_equal.
Qed.

Lemma variables_f_conj_list :
  forall a lf, variables_f (conj_list a lf) = Fset.Union _ (List.map (variables_f) lf).
Proof.
intros a lf; induction lf as [ | f1 lf].
- destruct a; rewrite conj_list_unfold; apply refl_equal.
- rewrite conj_list_unfold, variables_f_unfold, map_unfold, Fset.Union_unfold.
  apply f_equal; apply IHlf.
Qed.

Lemma free_variables_f_conj_list :
  forall a lf, free_variables_f (conj_list a lf) = Fset.Union _ (List.map (free_variables_f) lf).
Proof.
intros a lf; induction lf as [ | f1 lf].
- destruct a; rewrite conj_list_unfold; apply refl_equal.
- rewrite conj_list_unfold, free_variables_f_unfold, map_unfold, Fset.Union_unfold.
  apply f_equal; apply IHlf.
Qed.

Lemma conj_list_app :
  forall a lf1 lf2 I i,
    interp_formula I i (Conj a (conj_list a lf1) (conj_list a lf2)) =
    interp_formula I i (conj_list a (lf1 ++ lf2)).
Proof.
intros a l1; induction l1 as [ | a1 l1]; 
  intros l2 I i; 
  [destruct a; simpl; 
   [rewrite Bool.andb_true_l | rewrite Bool.negb_true, Bool.orb_false_l]; apply refl_equal | ].
assert (IH := IHl1 l2 I i); destruct a; simpl in IH; simpl.
- rewrite <- Bool.andb_assoc; apply f_equal; apply IH.
- rewrite <- Bool.orb_assoc; apply f_equal; apply IH.
Qed.

Lemma conj_list_Pcons_true :
  forall a lf1 f lf2 I i, interp_formula I i (conj_list a (f :: lf1 ++ lf2)) =
                       interp_formula I i (conj_list a (lf1 ++ f :: lf2)).
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros f l2 I i; [apply refl_equal | ].
assert (K := conj_swapp a f (Conj a a1 (conj_list a (l1 ++ l2))) I i).
simpl app.
rewrite 3 (conj_list_unfold _ (_ :: _)), K.
destruct a; simpl in IHl1; simpl.
- rewrite <- Bool.andb_assoc; apply f_equal; rewrite <- IHl1; apply Bool.andb_comm.
- rewrite <- Bool.orb_assoc; apply f_equal; rewrite <- IHl1; apply Bool.orb_comm.
Qed.

Lemma conj_list_permut_true :
  forall a lf1 lf2 I i, _permut (@eq _) lf1 lf2 -> 
                      interp_formula I i (conj_list a lf1) = 
                      interp_formula I i (conj_list a lf2).
Proof.
intros a l1; induction l1 as [ | a1 l1]; intros l2 I i H; inversion H; clear H; subst; 
[apply refl_equal | ].
rewrite <- conj_list_Pcons_true.
simpl; apply f_equal; apply IHl1; assumption.
Qed.

Lemma conj_and_list_true_iff :
  forall lf I i, interp_formula I i (conj_list And_F lf) = Bool.true B <->
                 (forall f, In f lf -> interp_formula I i f = Bool.true B).
Proof.
intro lf; induction lf as [ | f1 lf]; intros I i; simpl; split.
- intros _ f Abs; contradiction Abs.
- intros _; apply refl_equal.
- rewrite Bool.andb_true_iff; intros [H1 Hl] f [H | H].
  + subst f1; apply H1.
  + rewrite IHlf in Hl; apply Hl; assumption.
- intro H; rewrite (H f1); [ | left; apply refl_equal].
  rewrite Bool.andb_true_l, IHlf; intros; apply H; right; assumption.
Qed.

Lemma conj_and_list_false_iff :
  forall lf I i, interp_formula I i (conj_list And_F lf) = Bool.false B <->
                 (exists f, In f lf /\ interp_formula I i f = Bool.false B).
Proof.
intro lf; induction lf as [ | f1 lf]; intros I i; simpl; split.
- intro Abs; apply False_rec; apply (Bool.true_diff_false B Abs).
- intros [f [Abs _]]; contradiction Abs.
- rewrite Bool.andb_false_iff; intros [H | H].
  + exists f1; split; [left | ]; trivial.
  + rewrite IHlf in H; destruct H as [f [Hf Kf]].
    exists f; split; [right | ]; trivial.
- intros [f [[Hf | Hf] Kf]].
  + subst f; rewrite Kf, Bool.andb_false_l; apply refl_equal.
  + assert (Aux : interp_formula I i (conj_list And_F lf) = Bool.false B).
    {
      rewrite IHlf; exists f; split; assumption.
    }
    rewrite Bool.andb_comm, Aux, Bool.andb_false_l; apply refl_equal.
Qed.

Lemma conj_and_list_diff_false_iff :
  forall lf I i, interp_formula I i (conj_list And_F lf) <> Bool.false B <->
                 (forall f, In f lf -> interp_formula I i f <> Bool.false B).
Proof.
intro lf; induction lf as [ | f1 lf]; intros I i; simpl; split.
- intros _ f Abs; contradiction Abs.
- intros _; apply Bool.true_diff_false.
- rewrite Bool.andb_diff_false_iff; intros [Hf1 Hlf] f [Hf | Hf].
  + subst f; apply Hf1.
  + rewrite IHlf in Hlf; apply Hlf; assumption.
- intros H; rewrite Bool.andb_diff_false_iff; split.
  + apply H; left; apply refl_equal.
  + rewrite IHlf; intros f Hf; apply H; right; assumption.
Qed.

Lemma conj_or_list_true_iff :
  forall lf I i, interp_formula I i (conj_list Or_F lf) = Bool.true B <->
                 (exists f, In f lf /\ interp_formula I i f = Bool.true B).
Proof.
intro lf; induction lf as [ | f1 lf]; intros I i; simpl; split.
- intros Abs; apply False_rec.
  rewrite Bool.negb_true in Abs.
  apply (Bool.true_diff_false _ (sym_eq Abs)).
- intros [f [Abs _]]; contradiction Abs.
- rewrite Bool.orb_true_iff; intros [H1 | Hl].
  + exists f1; split; [left | ]; trivial.
  + rewrite IHlf in Hl.
    destruct Hl as [f [Hf Hl]]; exists f; split; [right | ]; trivial.
- intros [f [[H1 | Hl] H]].
  + subst f; rewrite H, Bool.orb_true_l.
    apply refl_equal.
  + rewrite Bool.orb_true_iff; right; rewrite IHlf.
    exists f; split; trivial.
Qed.

End Interp.

End Compare.

End Sec.

Arguments TTrue {dom} {predicate} {symbol}.

Require Import FlatData FiniteCollection FiniteBag.

Import Tuple.

Section SQL.

Hypothesis T : Tuple.Rcd.

Hypothesis dom : Type.
Hypothesis ODom : Oset.Rcd dom.
Hypothesis attributes_of_dom : dom -> Fset.set (A T).

Notation attribute := (attribute T).
Notation value := (value T).
Notation predicate := (predicate T).
Notation symb := (symbol T).
Notation aggregate := (aggregate T).
Notation tuple := (tuple T).
Notation funterm := (funterm T).
Notation aggterm := (aggterm T).
Notation select := (select T).
Notation group_by := (group_by T).
Arguments Select_As {T}.
Arguments Select_Star {T}.
Arguments Select_List {T}.
Arguments _Select_List {T}.
Notation OP := (OPred T).
Notation OSymb := (OSymb T).
Notation OAggregate := (OAgg T).
Notation B := (B T).
Notation interp_predicate := (interp_predicate T).
Notation interp_symb := (interp_symbol T).
Notation interp_aggregate := (interp_aggregate T).
Notation interp_aggterm :=  (interp_aggterm T).
Notation projection := (projection T).

Notation variable := (variable dom).
Notation setA := (Fset.set (A T)).
Notation BTupleT := (Fecol.CBag (CTuple T)).
Notation bagT := (Febag.bag BTupleT).
Notation listT := (list (tuple T)).
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

(*
(** * evaluation of SQL atoms *)
Definition eval_sql_atom env (a : sql_atom) : Bool.b B :=
  match a with
  | Sql_True => Bool.true B
  | Sql_Pred p l => interp_predicate p (map (interp_aggterm env) l)
  | Sql_Quant qtf p l  (Vrbl sq _) =>
    let lt := map (interp_aggterm env) l in
    interp_quant B qtf
                 (fun x => 
                    let la := Fset.elements _ (labels T x) in
                    interp_predicate p (lt ++ map (dot T x) la))
                 (Febag.elements _ (I sq))
  | Sql_In s sq => 
      if Febag.mem BTupleT (projection env (Select_List s)) (I sq)
      then Bool.true B
      else Bool.false B
  | Sql_Exists sq => 
      if Febag.is_empty _ (I sq) 
      then Bool.false B 
      else Bool.true B
  end.


(** * evaluation of SQL formulas *)
Fixpoint eval_sql_formula env (f : sql_formula) : Bool.b B := 
    match f with
    | Sql_Conj a f1 f2 => (interp_conj B a) (eval_sql_formula env f1) (eval_sql_formula env f2)
    | Sql_Not f => Bool.negb B (eval_sql_formula env f)
    | Sql_Atom a => eval_sql_atom env a
    end.
*)


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
| All_funterm : funterm -> All
| All_aggterm : aggterm -> All.

Hypothesis tree_of_dom : dom -> tree All.

Hypothesis size_of_dom_ge_one : forall sq, tree_size (tree_of_dom sq) >= 1.

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

(*
Lemma eval_sql_formula_eq_strong_etc :
  forall n,
    (forall q, tree_size (tree_of_dom q) <= n -> 
               forall env1 env2, equiv_env_strong T env1 env2 -> I env1 q =BE= I env2 q) ->
    forall f, tree_size (tree_of_sql_formula f) <= S n ->
              forall env1 env2, equiv_env_strong T env1 env2 -> 
                                eval_sql_formula env1 f = eval_sql_formula env2 f.
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
    apply (interp_aggterm_eq_strong T x _ _ He).
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
    assert (Aux := projection_eq T (Select_List s) _ _ He).
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

Lemma eval_sql_formula_eq_strong :
  forall env1 env2 f, equiv_env_strong env1 env2 ->
    eval_sql_formula env1 f = eval_sql_formula env2 f.
Proof.
Qed.

*)

End SQL.
