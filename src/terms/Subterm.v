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

Require Import Arith List Relations Bool.
Require Import BasicFacts ListFacts OrderedSet FiniteSet TransClosure.
Require Import Term Substitution.

Section Sec.
Hypothesis symbol : Type.
Hypothesis OF : Oset.Rcd symbol.

Hypothesis dom : Type.
Hypothesis OX : Oset.Rcd (variable dom).
Hypothesis FX : Fset.Rcd OX.

Notation term := (term dom symbol).

(** * Subterms in a term algebra.*)

Definition direct_subterm (t1 t2 : term) : Prop :=
  match t2 with
  | Var _ => False
  | Term _ l => In t1 l
  end.

Lemma size_direct_subterm :
 forall t1 t2, direct_subterm t1 t2 -> size t1 < size t2.
Proof.
intros t1 t2; case t2; clear t2.
intros a Abs; elim Abs.
intros f l; simpl; revert t1 l; clear f; fix size_direct_subterm 2.
intros t1 l; case l; clear l; simpl.
intro Abs; elim Abs.
intros t l t1_in_tl; case t1_in_tl; clear t1_in_tl.
intro t_eq_t1; subst t1; apply le_n_S; apply le_plus_l.
intro t_in_l; apply lt_le_trans with (1 + list_size (@size _ _) l).
simpl; apply size_direct_subterm; assumption.
apply le_n_S; apply le_plus_r.
Qed.

Fixpoint is_a_pos (t : term) (p : list nat) {struct p}: bool :=
  match p with
  | nil => true
  | i :: q =>
    match t with
    | Var _ => false
    | Term _ l => 
         match nth_error l i with
          | Some ti => is_a_pos ti q
          | None => false
          end
     end
  end.

Fixpoint subterm_at_pos (t : term) (p : list nat) {struct p}: option term :=
  match p with
  | nil => Some t
  | i :: q =>
    match t with
    | Var _ => None
    | Term _ l => 
         match nth_error l i with
          | Some ti => subterm_at_pos ti q
          | None => None
          end
    end
  end.

Definition is_subterm_bool := 
  fun (s : term) =>
    fix is_subterm_aux (t : term) : bool :=
  match t with 
    | Var x => 
      match s with Var y => Oset.eq_bool OX x y | _ => false end
    | Term _ l => 
      (Oset.eq_bool (OT OX OF) t s) || (existsb is_subterm_aux l)
  end.

Definition is_strict_subterm_bool s t :=
	match t with
	| Var _ => false
	| Term f l => existsb (is_subterm_bool s) l
	end.

Lemma is_a_pos_exists_subterm :
  forall t p, is_a_pos t p = true <-> exists u, subterm_at_pos t p = Some u.
Proof.
intros t p; revert t; induction p as [ | i q ].
intros t; split.
intros _; exists t; trivial.
intros _; trivial.
intros t; destruct t as [ x | f l ]; simpl; split.
intros; discriminate.
intros [u Abs]; discriminate.
destruct (nth_error l i) as [ ti | ].
intro; rewrite <- IHq; trivial.
intros; discriminate.
intros [u Sub]; destruct (nth_error l i).
rewrite IHq; exists u; trivial.
discriminate.
Qed.

Lemma subterm_at_pos_dec :
  forall t s, 
    {p : list nat | subterm_at_pos t p = Some s}+{forall p, subterm_at_pos t p <> Some s}.
Proof.
intro t; pattern t; apply term_rec3; clear t.
- intros x s; case s; clear s; [intro x'| intros f' l'].
  + case_eq (Oset.eq_bool OX x x').
    * intro x_eq_x'; rewrite Oset.eq_bool_true_iff in x_eq_x'; subst x'.
      left; exists nil; reflexivity.
    * {
        intro x_diff_x'; right; intros p; case p; clear p.
        - rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in x_diff_x'.
          intro H; apply x_diff_x'; injection H; clear H; intro H; exact H.
        - intros n p H; discriminate.
      }
  + right; intros p; case p; clear p.
    * intro H; discriminate.
    * intros n p H; discriminate.
- intros f l IHl s; case_eq (Oset.eq_bool (OT OX OF) (Term f l) s).
  + intro t_eq_s; rewrite Oset.eq_bool_true_iff in t_eq_s; subst s.
    left; exists nil; reflexivity.
  + intros t_diff_s; rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in t_diff_s.
    assert (IH : forall t, In t l -> forall s,  {p : list nat | subterm_at_pos t p = Some s} +
                       {(forall p : list nat, subterm_at_pos t p <> Some s)}).
    {
      clear - OF OX IHl.
      revert l IHl; fix subterm_at_pos_dec_list 1.
      intro l; case l; clear l.
        - intros t IHl Abs; elim Abs.
        - intros t1 l IHl t t_in_t1l; case_eq (Oset.eq_bool (OT OX OF) t t1).
          + intros t_eq_t1 s; rewrite Oset.eq_bool_true_iff in t_eq_t1; subst t1.
            apply IHl; left; trivial.
          + intros t_diff_t1 s; 
            apply (subterm_at_pos_dec_list l (fun x h => IHl _ (or_intror _ h)) t).
            simpl in t_in_t1l; case t_in_t1l; clear t_in_t1l.
            * intro t1_eq_t; subst t1; 
              rewrite Oset.eq_bool_refl in t_diff_t1; discriminate t_diff_t1.
            * exact (fun h => h).
    }
    * assert (IH' : forall s, 
                      {n :nat & {t : term & {p | (nth_error l n) = Some t /\ 
                                                 subterm_at_pos t p = Some s} } } + 
                      {(forall t, In t l -> forall p, subterm_at_pos t p <> Some s)}).
      {
        clear -IH.
        revert l IH; fix subterm_at_pos_dec 1.
        intro l; case l; clear l.
        - intros _ s; right; intros t Abs; elim Abs.
        - intros t l IH s.
          case (IH t (or_introl _ (refl_equal _)) s).
          + intro s_in_t; case s_in_t; intros p Sub; left; exists 0; exists t; exists p; split.
            * reflexivity.
            * assumption.
          + intro s_not_in_t; case (subterm_at_pos_dec l (fun x hx => IH x (or_intror _ hx)) s).
            intro s_in_l; case s_in_l; intros n H; case H; clear H; 
            intros tn H; case H; clear H; intros p H; case H; clear H; intros E Sub.
            * left; exists (S n); exists tn; exists p; split; assumption.
            * intro s_not_in_l; right.
              {
                intros t' t'_in_tl; simpl in t'_in_tl; case t'_in_tl.
                - intro t_eq_t'; rewrite <- t_eq_t'; exact s_not_in_t.
                - exact (s_not_in_l t').
              }
      }
      {
        case (IH' s); intro H.
        - case H; clear H; intros n H; case H; clear H; intros t H; case H; clear H; 
          intros p H; case H; clear H; intros E Sub.
          left; exists (n :: p); simpl; rewrite E; assumption.
        - right; intro p; case p; clear p.
          + simpl; intro t_eq_s; apply t_diff_s; injection t_eq_s; intro t_eq_s'; exact t_eq_s'.
          + intros n p; simpl.
            generalize (nth_error_some_in n l); case (nth_error l n).
            * intros tn H'; generalize (H' tn (refl_equal _)); clear H'; intro H'.
              apply (H tn H').
            * intros _; discriminate.
      }
Defined.

Lemma subterm_subterm_strong : 
	forall t i p s, subterm_at_pos t (i :: p) = Some s ->  trans_clos direct_subterm s t.
Proof.
intros [x | f l] i p s Sub; simpl in Sub; [discriminate | ].
revert f l i s Sub; induction p as [ | j p]; simpl; intros f l i s.
- case_eq (nth_error l i); 
  [intros ti Hi Ki; injection Ki; clear Ki; intro Ki; subst ti | intro Hi; discriminate].
  assert (Hl := nth_error_some_in _ _ Hi).
  left; apply Hl.
- case_eq (nth_error l i); [ | intro Hi; discriminate].
  intros ti Hi Ki.
  destruct ti as [ | g k]; [discriminate Ki | ].
  assert (Sub := IHp g k j s Ki).
  rewrite trans_clos_trans_clos_alt; right with (Term g k).
  + rewrite <- trans_clos_trans_clos_alt; assumption.
  + assert (Hl := nth_error_some_in _ _ Hi).
    apply Hl.
Qed.

Lemma subterm_subterm : 
	forall t p s, subterm_at_pos t p = Some s -> (t=s) \/ (trans_clos direct_subterm s t).
Proof.
intros t [ | i p] s Sub.
simpl in Sub; injection Sub; clear Sub; intro; left; assumption.
right; revert Sub; apply subterm_subterm_strong.
Qed.

Lemma subterm_in_subterm :
  forall p q t, subterm_at_pos t (p ++ q) = 
                         match subterm_at_pos t p with
                         | None => None
                         | Some s => subterm_at_pos s q
                         end.
Proof.
intro p; induction p as [ | i p]; intros q t; simpl.
apply refl_equal.
destruct t as [ | f l]; [apply refl_equal | ].
case (nth_error l i); [ | apply refl_equal].
intro; apply IHp.
Qed.

Lemma is_subterm_bool_ok_true : 
  forall s t, is_subterm_bool s t = true -> {p : list nat | subterm_at_pos t p = Some s}.
Proof.
intros s t; pattern t; apply term_rec3; clear t.
- destruct s as [y | ]; simpl; intros x H; [ | discriminate].
  exists nil; simpl; do 2 apply f_equal.
  rewrite Oset.eq_bool_true_iff in H; apply H.
- destruct s as [x | g k]; intros f l IHl H.
  + induction l as [ | t l]; [discriminate | ].
    case_eq (is_subterm_bool (Var x) t).
    * intro Sub; destruct (IHl _ (or_introl _ (refl_equal _)) Sub) as [p Sub'].
      exists (0 :: p); assumption.
    * {
        intro nSub; simpl in H; rewrite nSub in H; destruct IHl0 as [p Sub].
        - intros; apply IHl; [right | ]; assumption.
        - assumption.
        - destruct p as [ | i p].
          + discriminate.
          + exists (S i :: p); simpl; assumption.
      }
  + case_eq (Oset.eq_bool (OT OX OF) (Term f l) (Term g k)).
    * intro s_eq_t; exists nil.
      rewrite Oset.eq_bool_true_iff in s_eq_t; simpl; apply f_equal; apply s_eq_t.
    * intro s_diff_t; simpl in H; rewrite s_diff_t, Bool.orb_false_l in H.
      assert (H' : {i : nat & {p : list nat | subterm_at_pos (Term f l) (i :: p) = 
                                              Some (Term g k)} }).
      {
        clear s_diff_t; simpl; induction l as [ | t l].
        - discriminate.
        - case_eq (is_subterm_bool (Term g k) t).
          + intro Sub; destruct (IHl _ (or_introl _ (refl_equal _)) Sub) as [p Sub'].
            exists 0; exists p; assumption.
          + intro nSub; simpl in H; rewrite nSub in H.
            destruct IHl0 as [i [p Sub]].
            * intros; apply IHl; [right | ]; assumption.
            * assumption.
            * exists (S i); exists p; simpl; assumption.
      }
      destruct H' as [i [p Sub]]; exists (i :: p); assumption.
Defined.

Lemma is_subterm_ok_false : 
  forall s t, is_subterm_bool s t = false -> forall p, subterm_at_pos t p <> Some s.
Proof.
intros s t; pattern t; apply term_rec3; clear t.
- destruct s as [y | ]; simpl; intros x H [ | i p]; simpl.
  + intro Sub; rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in H.
    apply H; injection Sub; exact (fun h => h).
  + discriminate.
  + discriminate.
  + discriminate.
- destruct s as [x | g k]; intros f l IHl H.
  + intros [ | i p] Sub.
    * discriminate.
    * simpl in H, Sub.
      {
        revert i Sub; induction l as [ | t l].
        - intros [ | i] Sub ; discriminate.
        - intros i Sub; case_eq (is_subterm_bool (Var x) t).
          + intro Sub'; simpl in H; rewrite Sub' in H; discriminate.
          + intro nSub; simpl in H; rewrite nSub in H; destruct i as [ | i]; simpl in H.
            * apply (IHl _ (or_introl _ (refl_equal _)) nSub p Sub).
            * simpl in Sub.
              apply IHl0 with i; trivial.
              intros; apply IHl; [right | ]; trivial.
      }
  + intros [ | i p].
    * simpl; intro t_eq_s'.
      assert (t_eq_s : Term g k = Term f l).
      {
        injection t_eq_s'; intros; subst; apply refl_equal.
      } 
      clear t_eq_s'; rewrite t_eq_s in H; simpl in H.
      rewrite Oset.eq_bool_refl in H; discriminate H.
    * simpl; simpl in H.
      case_eq (nth_error l i); [ | discriminate].
      intros ti Hi Sub.
      assert (Abs : existsb (is_subterm_bool (Term g k)) l = true).
      {
        rewrite existsb_exists; exists ti; split.
        - apply (nth_error_some_in _ _ Hi).
        - case_eq (is_subterm_bool (Term g k) ti); [trivial | ].
          intro Abs; assert (IH := IHl ti (nth_error_some_in _ _ Hi) Abs _ Sub). 
          contradiction IH.
      }
      rewrite Abs, Bool.orb_true_r in H; discriminate H.
Qed.

Lemma size_subterm_at_pos :
  forall t i p, match subterm_at_pos t (i :: p) with
	           | Some u => size u < size t
	           | None => True
	           end.
Proof.
fix size_subterm_at_pos 3.
intros t i p; case p; clear p.
(* 1/2 *)
case t; clear t.
(* 1/3 *)
intro v; simpl; exact I.
(* 1/2 *)
intros f l; simpl subterm_at_pos.
generalize (nth_error_some_in i l); case (nth_error l i); [ | exact (fun _ => I)].
intros ti Hti; apply size_direct_subterm.
apply Hti; trivial.
(* 1/1 *)
intros j p; case t; clear t.
intro v; exact I.
set (q := j :: p) in *; assert (Hq := refl_equal q); unfold q at 2 in Hq; clearbody q.
intros f l; simpl subterm_at_pos.
generalize (nth_error_some_in i l); case (nth_error l i); [ | exact (fun _ => I)].
intros ti Hti.
rewrite Hq; generalize (size_subterm_at_pos ti j p).
case (subterm_at_pos ti (j :: p)); [ | exact (fun _ => I)].
intros t H1; apply lt_trans with (size ti); [assumption | ].
apply size_direct_subterm.
apply Hti; trivial.
Qed.

Lemma var_in_subterm_pos :
  forall v t, v inS variables_t FX t -> {p : list nat | subterm_at_pos t p = Some (Var v)}.
Proof.
intros v t; pattern t; apply term_rec3; clear t.
- intros x v_in_x; exists (@nil nat); simpl; do 2 apply f_equal.
  rewrite in_variables_t_var in v_in_x; assumption.
- intros f l; simpl.
  induction l as [ | t l]; intros IH v_in_l; rewrite Fset.Union_unfold in v_in_l.
  + rewrite Fset.empty_spec in v_in_l; discriminate v_in_l.
  + rewrite map_unfold, Fset.mem_union in v_in_l.
    case_eq (v inS? variables_t FX t); intro v_in_t.
    * destruct (IH t (or_introl _ (refl_equal _)) v_in_t) as [p Sub].
      exists (0 :: p); simpl; trivial.
    * rewrite v_in_t, Bool.orb_false_l in v_in_l.
      destruct (IHl (fun x x_in_l =>  IH x (or_intror _ x_in_l)) v_in_l) as [p Sub]; trivial.
      {
        destruct p as [ | i p]; simpl in Sub.
        - discriminate.
        - exists (S(i) :: p); simpl; trivial.
      }
Qed.

Lemma var_in_subterm_var_in_term :
  forall v s t p, subterm_at_pos t p = Some s -> v inS variables_t FX s -> v inS variables_t FX t.
Proof.
intros v s t p; revert s t; induction p as [ | i p]; intros s t H v_in_s.
simpl in H; injection H; clear H; intros; subst; trivial.
simpl in H; destruct t as [ | g l].
discriminate.
assert (H' := nth_error_some_in i l).
destruct (nth_error l i) as [ti | ].
- assert (H'' := H' _ (refl_equal _)).
  rewrite variables_t_unfold, Fset.mem_Union.
  exists (variables_t FX ti); split.
  + rewrite in_map_iff; exists ti; split; trivial.
  + apply (IHp _ _ H v_in_s).
- discriminate H.
Qed.

Fixpoint replace_at_pos (t u : term) (p : list nat) {struct p} : term :=
  match p with
  | nil => u
  | i :: q =>
     match t with
     | Var _ => t
     | Term f l =>
        let replace_at_pos_list :=
         (fix replace_at_pos_list j (l : list term) {struct l}: list term :=
            match l with
            | nil => nil
            | h :: tl =>
                 match j with
                 | O => (replace_at_pos h u q) :: tl
                 | S k => h :: (replace_at_pos_list k tl)
                 end
            end) in
    Term f (replace_at_pos_list i l)
    end
  end.

Fixpoint replace_at_pos_list (u : term) (i : nat) (p : list nat) (l : list term)
 {struct l}: list term :=
  match l with
  | nil => nil
  | h :: tl =>
     match i with
     | O => (replace_at_pos h u p) :: tl
     | S j => h :: (replace_at_pos_list u j p tl)
     end
  end.

Lemma replace_at_pos_unfold :
  forall f l u i q,
   replace_at_pos (Term f l) u (i :: q) = Term f (replace_at_pos_list u i q l).
Proof.
intros f l u i q; simpl; apply (f_equal (fun l => Term f l)); 
generalize u i q; clear u i q; 
induction l as [| t l]; intros u i q; trivial.
simpl; destruct i as [ | i ]; trivial.
rewrite <- IHl; trivial.
Qed.

Lemma replace_at_pos_replace_at_pos :
  forall t u u' p, replace_at_pos (replace_at_pos t u' p) u p = replace_at_pos t u p.
Proof.
intros t u u' p; revert t u u'; induction p as [ | i p]; intros t u u'.
apply refl_equal.
destruct t as [x | f l].
simpl; apply refl_equal.
rewrite 3 replace_at_pos_unfold.
apply f_equal.
revert i; induction l as [ | t l]; intro i.
apply refl_equal.
destruct i as [ | i]; simpl.
apply f_equal2; [apply IHp | apply refl_equal].
apply f_equal; apply IHl.
Qed.

Lemma replace_at_pos_is_replace_at_pos1 :
  forall t u p, is_a_pos t p = true ->
  subterm_at_pos (replace_at_pos t u p) p = Some u.
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros x u p; destruct p as [ | i q ]; trivial;
intros; discriminate.
intros f l IHl u p; destruct p as [ | i q ]; trivial.
rewrite replace_at_pos_unfold; simpl; generalize i q; clear i q; 
induction l as [ | t l ]; intros i q.
destruct i as [ | i ]; simpl; intros; discriminate.
destruct i as [ | i ]; simpl.
intros; apply (IHl t); trivial; left; trivial.
intros; apply IHl0; intros; trivial; apply IHl; trivial; right; trivial.
Qed.

Lemma replace_at_pos_is_replace_at_pos2 :
  forall t p u, subterm_at_pos t p = Some u -> replace_at_pos t u p = t. 
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v p u; destruct p as [ | i q ]; intro H; inversion_clear H; trivial.
intros f l IHl p; destruct p as [ | i q ]. 
intros u H; inversion_clear H; trivial.
intros u H; rewrite replace_at_pos_unfold; 
apply (f_equal (fun l => Term f l)); generalize i q u H; clear i q u H;
induction l as [ | t l ]; intros i q u H.
destruct i as [ | i ]; simpl; intros; discriminate.
destruct i as [ | i ]; simpl.
rewrite IHl; trivial; left; trivial.
rewrite IHl0; trivial; intros; apply IHl; trivial; right; trivial.
Qed.

Lemma replace_at_pos_list_replace_at_pos_in_subterm :
forall l1 ui l2 u i p, length l1 = i ->
 replace_at_pos_list  u i p (l1 ++ ui :: l2) = 
 l1 ++ (replace_at_pos ui u p) :: l2.
Proof.
intros l1; induction l1 as [ | u1 l1 ]; intros ui l2 u i p L; simpl in L.
subst i; trivial.
destruct i as [ | i ].
discriminate.
simpl; rewrite IHl1; trivial.
inversion L; trivial.
Qed.

(** ** Substitutions and Subterms. *)

Lemma instantiated_subterm :
  forall (u u' : term) sigma, trans_clos direct_subterm u u' -> 
   trans_clos direct_subterm (apply_subst OX sigma u)  (apply_subst OX sigma u').
Proof.
intros u u' sigma; apply trans_clos_incl_of.
intros s [ | f l] s_in_l.
contradiction.
simpl; rewrite in_map_iff; exists s; split; trivial.
Qed.
 
Lemma subterm_at_pos_apply_subst_apply_subst_subterm_at_pos :
  forall (t : term) p sigma u, subterm_at_pos t p = Some u ->
        subterm_at_pos (apply_subst OX sigma t) p = Some (apply_subst OX sigma u).
Proof.
intro t; pattern t; apply term_rec3; clear t.
intros v p sigma u H; destruct p as [ | i q ]; simpl; trivial.
simpl in H; injection H; clear H; intros; subst; apply refl_equal.
discriminate.
intros f l IH p sigma u H; destruct p as [ | i q ]; simpl.
simpl in H; injection H; clear H; intros; subst; apply refl_equal.
revert i H; simpl; induction l as [ | t l]; intros i H; destruct i as [ | i].
discriminate.
discriminate.
simpl; simpl in H; apply IH; [left; apply refl_equal | assumption].
simpl; simpl in H.
apply IHl.
intros; apply IH; [right | ]; assumption.
assumption.
Qed.

End Sec.

