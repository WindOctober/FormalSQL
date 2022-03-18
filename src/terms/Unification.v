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
Require Import BasicFacts ListFacts OrderedSet FiniteSet.
Require Import Term Substitution Subterm.

Section Sec.
Hypothesis symbol : Type.
Hypothesis OF : Oset.Rcd symbol.

Hypothesis dom : Type.
Hypothesis OX : Oset.Rcd (variable dom).
Hypothesis FX : Fset.Rcd OX.

Notation term := (term dom symbol).

Record unification_problem : Type :=
  mk_pb 
  {
    solved_part : substitution dom symbol;
    unsolved_part : list (term * term)
  }.

Inductive exc (A : Type) : Type :=
  | Normal : A -> exc A
  | Not_appliable : A -> exc A
  | No_solution : exc A.

Fixpoint combine A (l : list (A * A))  (l1 l2 : list A) {struct l1} : list (A * A) :=
  match l1, l2 with
  | nil, _ => l
  | _, nil => l
  | (a1 :: l1), (a2 :: l2) => combine ((a1,a2) :: l) l1 l2
  end.

Definition decomposition_step (pb : unification_problem) : exc unification_problem :=
   match pb.(unsolved_part) with
   | nil => @Not_appliable _ pb
   | (s,t) :: l =>
      if Oset.eq_bool (OT OX OF) s t 
      then Normal (mk_pb pb.(solved_part) l)
      else
        match s, t with
      | Var x, Var y => 
        let x_maps_to_y := (x, t) :: nil in
        let solved_part' := 
            map (fun vv_sigma => match vv_sigma with
                                     | (v, v_sigma) =>
                                       (v, apply_subst OX x_maps_to_y v_sigma)
                                 end)
                              pb.(solved_part) in
        let l' := map (fun uv => match uv with
                                     | (u,v) => (apply_subst OX ((x, t) :: nil) u,
                                                  apply_subst OX ((x, t) :: nil) v)
                                 end) l in
         match Oset.find OX x solved_part' with
         | Some x_val => Normal (mk_pb ((x, t) :: solved_part') ((t, x_val) :: l'))
         | None => Normal (mk_pb ((x, t) :: solved_part') l')
         end
      | Var x, (Term _ _ as u) 
      | (Term _ _ as u), Var x => 
        match Oset.find OX x pb.(solved_part) with
        | None => Normal (mk_pb ((x, u) :: pb.(solved_part)) l)
        | Some (Term _ _ as x_val) => 
          match Oset.compare Onat (size u) (size x_val) with
            | Lt => Normal (mk_pb ((x, u) :: pb.(solved_part)) ((x_val, u) :: l))
            | _ => Normal (mk_pb pb.(solved_part) ((x_val, u) :: l))
          end
      | Some (Var _) => @Not_appliable _ pb
        end
      | Term f l1, Term g l2 => 
         if Oset.eq_bool OF f g
         then 
             match Oset.eq_bool Onat (length l1) (length l2) with
             | true => Normal (mk_pb pb.(solved_part) (combine l l1 l2))
             | false => @No_solution _
             end
         else @No_solution _
      end
   end.

Definition is_a_solution pb theta :=
  (forall s t, In (s, t) (unsolved_part pb) -> apply_subst OX theta s = apply_subst OX theta t) /\
  (forall x x_val, Oset.find OX x (solved_part pb) = Some x_val -> 
                   apply_subst OX theta (Var x) = apply_subst OX theta x_val).


(*
Definition is_a_strong_solution pb theta :=
  (forall s t, In (s, t) pb.(unsolved_part) -> apply_subst OX theta s = apply_subst OX theta t) /\
 (forall x x_val, In (x, x_val) pb.(solved_part) -> 
                  apply_subst OX theta (Var _ x) = apply_subst OX theta x_val).
*)

Lemma var_rep_aux : 
  forall theta x s , apply_subst OX theta (Var (symbol := symbol) x) = apply_subst OX theta s ->
  forall t, apply_subst OX theta t = apply_subst OX theta (apply_subst OX ((x, s) :: nil) t).
Proof.
intros theta x s H t.
rewrite apply_subst_apply_subst, <- (apply_subst_eq_1 FX).
intros z z_in_t; simpl.
case_eq (Oset.eq_bool OX z x); intro Hz.
- rewrite Oset.eq_bool_true_iff in Hz; subst z.
  rewrite <- H; apply refl_equal.
- apply refl_equal.
Qed.

Lemma decomposition_step_is_sound :
 forall l sigma theta, 
  match decomposition_step (mk_pb sigma l)  with
  | Normal pb' => is_a_solution pb' theta -> is_a_solution (mk_pb sigma l) theta
  | No_solution _ => is_a_solution (mk_pb sigma l) theta -> False
  | Not_appliable pb' => 
    is_a_solution pb' theta -> is_a_solution (mk_pb sigma l) theta
  end.
Proof.
intros [ | [s t] l]  sigma theta; 
unfold is_a_solution, decomposition_step; 
simpl solved_part; simpl unsolved_part; cbv iota beta; trivial.
case_eq (Oset.eq_bool (OT OX OF) s t); [intro s_eq_t | intro s_diff_t].
- (* 1/2 remove trivial eq *)
  rewrite Oset.eq_bool_true_iff in s_eq_t.
  intros [Hl Hsigma]; split; [ | intros; apply Hsigma; trivial].
  intros s' t' [H | H]; [ | apply Hl; assumption].
  injection H; clear H; intros; subst s s' t'; apply refl_equal.
- (* 1/1 *)
  destruct s as [ x | f l1 ]; destruct t as [ y | g l2 ]. 
  + (* 1/4 Coalesce *)
    case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
    * (* 1/5 *)
      rewrite (Oset.find_some_map OX _ _ _ x_sigma); intros [Hl Hsigma].
      simpl solved_part in *; simpl unsolved_part in *.
      assert (Hxy : apply_subst OX theta (Var x) = apply_subst OX theta (Var y)).
      {
        apply (Hsigma x (Var y)); simpl; rewrite Oset.eq_bool_refl; trivial.
      }
      {
        split.
        - (* 1/6 *)
          intros s t [H | H].
          + injection H; clear H; intros; subst s t; apply Hxy.
          + rewrite (var_rep_aux theta x (Var y) Hxy s), (var_rep_aux theta x (Var y) Hxy t).
            apply Hl; right; rewrite in_map_iff;
            exists (s,t); split; [apply refl_equal | assumption].
        - (* 1/5 *)
          intros z s H.
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
          + rewrite Oset.eq_bool_true_iff in z_eq_x; subst z. 
            rewrite x_sigma in H; injection H; clear H; intro H; subst s.
            rewrite Hxy.
            rewrite (Hl _ _ (or_introl _ (refl_equal _))).
            apply sym_eq; apply var_rep_aux; assumption.
          + rewrite (Hsigma z (apply_subst OX ((x, Var y) :: nil) s)).
            * apply sym_eq; apply var_rep_aux; assumption.
            * simpl; rewrite z_diff_x, (Oset.find_some_map _ _ _ _ H); apply refl_equal.
      }
    * rewrite (Oset.find_none_map OX _ _ _ x_sigma); intros [Hl Hsigma]; 
      simpl solved_part in *; simpl unsolved_part in *.
      assert (Hxy : apply_subst OX theta (Var x) = apply_subst OX theta (Var y)).
      {
        apply (Hsigma x (Var y)); simpl; rewrite Oset.eq_bool_refl; trivial.
      }
      { (* 1/4 *)
        split.
        - (* 1/5 *)
          intros s t [H | H].
          + injection H; clear H; intros; subst s t; trivial.
          + rewrite (var_rep_aux theta x (Var y) Hxy s), (var_rep_aux theta x (Var y) Hxy t).
            apply Hl; simpl.
            rewrite in_map_iff; exists (s,t); split; [apply refl_equal | assumption].
        - (* 1/4 *)
          intros z s H.
          rewrite (var_rep_aux theta x (Var y) Hxy s).
          apply (Hsigma z (apply_subst OX ((x, Var y) :: nil) s)).
          simpl; rewrite (Oset.find_some_map _ _ _ _ H).
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x; trivial].
          rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          rewrite x_sigma in H; discriminate H.
      } 
  + { (* 1/3 Merge *)
      case_eq (Oset.find OX x sigma); [intros [y | f k] x_sigma | intro x_sigma].
      - (* 1/5 *)
        exact (fun h => h).
      - (* 1/4 *)
        case (Oset.compare Onat (size (Term g l2)) (size (Term f k))).
        + (* /5 *)
          simpl; intros [Hl Hsigma]; split; [ | apply Hsigma].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Term f k)).
          * apply Hsigma; trivial.
          * apply Hl; left; apply refl_equal.
        + (* 1/4 *)
          simpl; intros [Hl Hsigma]; split.
          * intros s t [H | H]; [ | apply Hl; right; assumption].
            injection H; clear H; intros; subst; apply Hsigma.
            rewrite Oset.eq_bool_refl; trivial.
          * intros z z_val z_sigma.
            {
              case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
              - rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
                rewrite x_sigma in z_sigma; injection z_sigma; clear z_sigma; intro; subst z_val.
                rewrite (Hl _ _ (or_introl _ (refl_equal _))).
                apply Hsigma; rewrite Oset.eq_bool_refl; trivial.
              - apply Hsigma; rewrite z_diff_x; trivial.
            }
        + (* 1/5' *)
          simpl; intros [Hl Hsigma]; split; [ | apply Hsigma].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Term f k)); 
            [apply Hsigma; trivial | apply Hl; left; apply refl_equal].
      - (* 1/3 *)
        intros [Hl Hsigma]; split.
        + intros s t [H | H].
          * injection H; clear H; intros; subst s t; apply Hsigma; simpl.
            rewrite Oset.eq_bool_refl; trivial.
          * apply Hl; assumption.
        + intros z z_val z_sigma; apply Hsigma; simpl.
          rewrite z_sigma; 
            case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x; trivial].
          rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          rewrite x_sigma in z_sigma; discriminate z_sigma.
    } 
  + { (* 1/2 Merge (sym) *)
      case_eq (Oset.find OX y sigma); [intros [x | g k] y_sigma | intro y_sigma].
      - (* 1/4 *)
        exact (fun h => h).
      - (* 1/3 *)
        case (Oset.compare Onat (size (Term f l1)) (size (Term g k))).
        + (* 1/4 *)
          simpl; intros [Hl Hsigma]; split; [ | apply Hsigma].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Term g k)).
          * apply sym_eq; apply Hl; left; apply refl_equal.
          * apply sym_eq; apply Hsigma; trivial.
        + (* 1/3 *)
          simpl; intros [Hl Hsigma]; split.
          * intros s t [H | H]; [ | apply Hl; right; assumption].
            injection H; clear H; intros; subst s t; apply sym_eq; apply Hsigma.
            rewrite Oset.eq_bool_refl; trivial.
          * intros z z_val z_sigma.
            {
              case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
              - rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
                rewrite y_sigma in z_sigma; injection z_sigma; clear z_sigma; intro; subst z_val.
                rewrite (Hl _ _ (or_introl _ (refl_equal _))).
                apply Hsigma; rewrite Oset.eq_bool_refl; trivial.
              - apply Hsigma; rewrite z_diff_y; trivial.
            }
        + (* 1/4' *)
          simpl; intros [Hl Hsigma]; split; [ | apply Hsigma].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Term g k)).
          * apply sym_eq; apply Hl; left; apply refl_equal.
          * apply sym_eq; apply Hsigma; trivial.
      - (* 1/2 *)
        intros [Hl Hsigma]; split.
        + intros s t [H | H].
          * injection H; clear H; intros; subst s t;
            apply sym_eq; apply Hsigma; simpl; rewrite Oset.eq_bool_refl; trivial.
          * apply Hl; assumption.
        + intros z z_val z_sigma; apply Hsigma; simpl; rewrite z_sigma.
          case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y; trivial].
          rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
          rewrite y_sigma in z_sigma; discriminate z_sigma.
    }
  + { (* 1/1 Decomposition *)
      case_eq (Oset.eq_bool OF f g); [intro f_eq_g | intro f_diff_g].
      - (* 1/2 *)
        rewrite Oset.eq_bool_true_iff in f_eq_g; subst g.
        case_eq (Oset.eq_bool Onat (length l1) (length l2)); intro L.
        + (* 1/3 *)
          simpl; intros [Hl Hsigma].
          split; [ | apply Hsigma].
          assert ((forall s t, In (s,t) l -> apply_subst OX theta s = apply_subst OX theta t) /\
             map (apply_subst OX theta) l1 = map (apply_subst OX theta) l2).
          {
            generalize l2 l L  Hl; clear l2 L l Hl s_diff_t; 
            induction l1 as [ | s1 l1];
            intros [ | s2 l2] l L Hl.
            - split; trivial; apply Hl; trivial.
            - discriminate.
            - discriminate.
            - assert (H : forall s t : term, In (s, t) ((s1,s2) :: l) -> 
                                             apply_subst OX theta s = apply_subst OX theta t).
              { 
                intros s t H; refine (proj1 (IHl1 l2 _ _ _) s t H); clear s t H.
                - rewrite Oset.eq_bool_true_iff in L; simpl in L; injection L.
                  rewrite Oset.eq_bool_true_iff; exact (fun h => h).
                - intros s t H; apply Hl; trivial.
              } 
              split.
              + intros s t s_t_in_l; apply H; right; trivial.
              + simpl; rewrite (H s1 s2); [apply f_equal | left; trivial].
                refine (proj2 (IHl1 l2 _ _ Hl)).
                rewrite Oset.eq_bool_true_iff in L; simpl in L; injection L.
                rewrite Oset.eq_bool_true_iff; exact (fun h => h).
          } 
          intros s t [s_t_eq_f_l1_g_l2 | s_t_in_l].
          * injection s_t_eq_f_l1_g_l2; intros; subst; simpl; 
            destruct H as [ _ H ]; rewrite H; subst; trivial.
          * destruct H as [ H _ ]; apply H; trivial.
        + (* 1/2 *)
          intros [Hl Hsigma].
          generalize (Hl _ _ (or_introl _ (refl_equal _))); 
          intro H; injection H; clear H; intros H.
          generalize (f_equal (@length _) H).
          rewrite 2 map_length; clear H; intro H; rewrite <- H, Oset.eq_bool_refl in L.
          discriminate L.
      - (* 1/1 *)
        intros [Hl Hsigma].
        rewrite <- not_true_iff_false in f_diff_g.
        apply f_diff_g.
        assert (Abs := Hl _ _ (or_introl _ (refl_equal _))); simpl in Abs; injection Abs;
        intros _ H; rewrite H, Oset.eq_bool_true_iff; trivial.
}
Qed.

Lemma decomposition_step_is_complete :
 forall l sigma theta, is_a_solution (mk_pb sigma l) theta ->
  match decomposition_step (mk_pb sigma l)  with
  | Normal pb' => is_a_solution pb' theta
  | No_solution _ => False
  | Not_appliable pb' => is_a_solution pb' theta
  end.
Proof.
intros [ | [s t] l]  sigma theta; 
unfold decomposition_step; simpl unsolved_part; cbv iota beta; trivial.
case_eq (Oset.eq_bool (OT OX OF) s t); [intro s_eq_t | intro s_diff_t].
- (* 1/2 remove trivial eq *)
  unfold is_a_solution; simpl solved_part; simpl unsolved_part;
  intros [Hl Hsigma]; split; [intros; apply Hl; right | intros; apply Hsigma]; trivial.
- (* 1/1 *)
  + destruct s as [ x | f l1 ]; destruct t as [ y | g l2 ]; unfold is_a_solution.
  * (* 1/4 Coalesce *)
    intros [Hl Hsigma].
    {
      case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
      - (* 1/5 *)
        rewrite (Oset.find_some_map _ _ _ _ x_sigma); simpl; split.
        + (* 1/6 *)
          intros s t [H | H].
          * (* 1/7 *)
            injection H; intros; subst s t; 
            rewrite <- (var_rep_aux _ _ _ (Hl _ _ (or_introl _ (refl_equal _)))).
            apply trans_eq with (apply_subst OX theta (Var x)).
            apply sym_eq; apply Hl; left; apply refl_equal.
            apply Hsigma; trivial.
          * (* 1/6 *)
            rewrite in_map_iff in H; destruct H as [[s' t'] [K1 K2]].
            injection K1; clear K1; intros; subst s t; 
            rewrite <- 2 (var_rep_aux _ _ _ (Hl _ _ (or_introl _ (refl_equal _)))); 
            apply Hl; right; assumption.
        + (* 1/5 *)
          simpl; intros z s H.
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
          * rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
            rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst s.
            apply (Hl _ _ (or_introl _ (refl_equal _))).
          * rewrite z_diff_x in H.
            {
              case_eq (Oset.find OX z sigma); [intros z_val z_sigma | intro z_sigma].
              - rewrite (Oset.find_some_map _ _ _ _ z_sigma) in H.
                injection H; clear H; intro H; subst s.
                assert (H := Hsigma z z_val z_sigma); simpl in H; rewrite H.
                apply (var_rep_aux _ _ _ (Hl _ _ (or_introl _ (refl_equal _)))).
              - rewrite (Oset.find_none_map _ _ _ _ z_sigma) in H; discriminate H.
            }
      - (* 1/4 *)
        rewrite (Oset.find_none_map OX _ _ _ x_sigma); simpl; split.
        + (* 1/5 *)
          intros s t H; rewrite in_map_iff in H; destruct H as [[s' t'] [K1 K2]].
          injection K1; clear K1; intros; subst s t; 
          rewrite <- 2 (var_rep_aux _ _ _ (Hl _ _ (or_introl _ (refl_equal _)))).
          apply Hl; right; assumption.
        + (* 1/4 *)
          simpl; intros z s H.
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
          * rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
            rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst s.
            apply (Hl _ _ (or_introl _ (refl_equal _))).
          * rewrite z_diff_x in H.
            {
              case_eq (Oset.find OX z sigma); [intros z_val z_sigma | intro z_sigma].
              - rewrite (Oset.find_some_map _ _ _ _ z_sigma) in H.
                injection H; clear H; intro H; subst s.
                assert (H := Hsigma z z_val z_sigma); simpl in H; rewrite H.
                apply (var_rep_aux _ _ _ (Hl _ _ (or_introl _ (refl_equal _)))).
              - rewrite (Oset.find_none_map _ _ _ _ z_sigma) in H; discriminate H.
            }
    }
  * (* 1/3  Merge *)
    intros [Hl Hsigma]; unfold is_a_solution.
    {
      case_eq (Oset.find OX x sigma); [intros [y | f k] x_sigma | intro x_sigma]; 
      simpl solved_part; rewrite x_sigma.
      - (* 1/5 *)
        split; assumption.
      - (* 1/4 *)
        case (Oset.compare Onat (size (Term g l2)) (size (Term f k))).
        + split;  [ | apply Hsigma; assumption].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Var x)).
          * apply sym_eq; apply Hsigma; trivial.
          * apply Hl; left; apply refl_equal.
        + (* 1/4 *)
          split.
          * (* 1/5 *)
            intros s t [H | H]; [ | apply Hl; right; assumption].
            injection H; clear H; intros; subst s t.
            {
              apply trans_eq with (apply_subst OX theta (Var x)).
              - apply sym_eq; apply Hsigma; trivial.
              - apply Hl; left; apply refl_equal.
            } 
          * (* 1/4 *)
            intros z t H; simpl in H.
            {
              case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
              - rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
                rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst t.
                apply (Hl _ _ (or_introl _ (refl_equal _))).
              - rewrite z_diff_x in H; apply (Hsigma z t H).
            }
        + split;  [ | apply Hsigma; assumption].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Var x)).
          * apply sym_eq; apply Hsigma; trivial.
          * apply Hl; left; apply refl_equal.
      - (* 1/3 *)
        split;  [intros; apply Hl; right; assumption | ].
        intros z s H; simpl in H.
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        + rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst s.
          apply (Hl _ _ (or_introl _ (refl_equal _))).
        + rewrite z_diff_x in H; apply (Hsigma z s H).
    } 
  * (* 1/2 Merge (sym) *)
    intros [Hl Hsigma]; unfold is_a_solution.
    {
      case_eq (Oset.find OX y sigma); [intros [x | g k] y_sigma | intro y_sigma]; 
      simpl solved_part; rewrite y_sigma.
      - (* 1/4 *)
        split; assumption.
      - (* 1/3 *)
        case (Oset.compare Onat (size (Term f l1)) (size (Term g k))).
        + (* 1/4 *)
          split;  [ | apply Hsigma; assumption].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Var y)).
          * apply sym_eq; apply Hsigma; trivial.
          * apply sym_eq; apply Hl; left; apply refl_equal.
        + (* 1/3 *)
          split.
          * (* 1/4 *)
            intros s t [H | H]; [ | apply Hl; right; assumption].
            injection H; clear H; intros; subst s t.
            {
              apply trans_eq with (apply_subst OX theta (Var y)).
              - apply sym_eq; apply Hsigma; trivial.
              - apply sym_eq; apply Hl; left; apply refl_equal.
            }
          * (* 1/4 *)
            intros z t H; simpl in H.
            {
              case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
              - rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
                rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst t.
                apply sym_eq; apply (Hl _ _ (or_introl _ (refl_equal _))).
              - rewrite z_diff_y in H; apply (Hsigma z t H).
            }
        + (* 1/4' *)
          split;  [ | apply Hsigma; assumption].
          intros s t [H | H]; [ | apply Hl; right; assumption].
          injection H; clear H; intros; subst s t.
          apply trans_eq with (apply_subst OX theta (Var y)).
          * apply sym_eq; apply Hsigma; trivial.
          * apply sym_eq; apply Hl; left; apply refl_equal.
      - (* 1/3 *)
        split;  [intros; apply Hl; right; assumption | ].
        intros z t H; simpl in H.
        case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
        + rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
          rewrite Oset.eq_bool_refl in H; injection H; clear H; intro H; subst t.
          apply sym_eq; apply (Hl _ _ (or_introl _ (refl_equal _))).
        + rewrite z_diff_y in H; apply (Hsigma z t H).
    }
  * (* 1/1 Decomposition *)
    intros [Hl Hsigma]; unfold is_a_solution.
    {
      case_eq (Oset.eq_bool OF f g); [intro f_eq_g | intro f_diff_g].
      - (* 1/2 *)
        case_eq (Oset.eq_bool Onat (length l1) (length l2)); intro L.
        + (* 1/3 *)
          split; [ | apply Hsigma].
          assert (Hl' : forall s t, In (s,t) l -> apply_subst OX theta s = apply_subst OX theta t).
          {
            intros; apply Hl; right; trivial.
          } 
          assert (Hl12 : map (apply_subst OX theta) l1 = map (apply_subst OX theta) l2).
          {
            generalize (Hl _ _ (or_introl _ (refl_equal _))); simpl; 
            intro H; injection H; intros; trivial.
          }
          clear Hsigma; generalize l2 l L Hl' Hl12; clear s_diff_t l2 l L Hl Hl' Hl12; 
          induction l1 as [ | s1 l1]; intros [ | s2 l2] l L Hl Hl12.
          * intros s t; simpl; intros s_t_in_l; apply Hl; trivial.
          * discriminate.
          * discriminate.
          * simpl unsolved_part.
            intros s t s_t_in_l'; refine (IHl1 l2 _ _ _ _ _ _ s_t_in_l'); clear s t s_t_in_l'.
            apply L.
            {
              intros s t [s_t_eq_s1_s2 | s_t_in_l].
              - injection s_t_eq_s1_s2; simpl in Hl12; injection Hl12; intros; subst s t; trivial.
              - apply Hl; trivial.
            }
            simpl in Hl12; injection Hl12; intros; trivial.
        + generalize (Hl _ _ (or_introl _ (refl_equal _))); simpl; 
          intro H; injection H; intros H' _.
          generalize (f_equal (@length _) H'); clear H'; 
          intro H'; rewrite 2 map_length in H'; rewrite <- H', Oset.eq_bool_refl in L.
          discriminate L.
      - generalize (Hl _ _ (or_introl _ (refl_equal _))); simpl; intro H; injection H; intros _ H'.
        rewrite <- not_true_iff_false in f_diff_g.
        apply f_diff_g; apply Oset.eq_bool_true_iff; assumption.
    }
Qed.

Fixpoint decompose n pb :=
 match n with
| 0 => Some pb
| S m => 
    match decomposition_step pb with
    | Normal pb' => decompose m pb'
    | No_solution _ => None
    | Not_appliable pb' => Some pb'
    end
end.

Definition substitution_to_eq_list (sigma : substitution dom symbol) :=
  map (fun x => (Var (symbol := symbol) x, apply_subst OX sigma (Var x))) 
      ({{{domain_of_subst FX sigma}}}).

Definition set_of_variables_in_eq_list (l : list (term * term)) : Fset.set FX :=
  Fset.Union 
    _ (map (fun tt => Fset.union _ (variables_t FX (fst tt)) (variables_t FX (snd tt))) l).

Definition set_of_variables_in_range_of_subst (sigma : substitution dom symbol) : Fset.set FX :=
  Fset.Union _ (map (fun xt => variables_t FX (snd xt)) sigma).

Definition vars_of_pb pb := 
  (set_of_variables_in_eq_list pb.(unsolved_part)) unionS
    (set_of_variables_in_eq_list (substitution_to_eq_list pb.(solved_part))).

Definition is_a_solved_var x pb :=
  match Oset.find OX x pb.(solved_part) with
    | Some _ =>
      (negb (x inS? set_of_variables_in_eq_list (unsolved_part pb))) 
        && negb (x inS? set_of_variables_in_range_of_subst (solved_part pb))%bool
    | None => false
  end.

Definition phi1 pb :=
   Fset.cardinal _ (Fset.filter _ (fun v => negb (is_a_solved_var v pb)) (vars_of_pb pb)).

Fixpoint size_minus (f : nat -> nat) t1 t2 :=
 match t1, t2 with
 | Var _, Var _ => 0
 | Var _, _ => f 1
 | _, Var _ => f (size t1)
 | Term _ l1, Term _ l2 =>
     let fix size_minus_list (l1 l2 : list term) {struct l1} : nat :=
       match l1, l2 with
       | nil, _ => 0
       | t1 :: l1 , nil => f (size t1) + size_minus_list l1 l2
       | u1 :: l1, u2 :: l2 => size_minus f u1 u2 + size_minus_list l1 l2
       end in
       size_minus_list l1 l2
  end.

Fixpoint size_minus_list f l1 l2 :=
   match l1, l2 with
       | nil, _ => 0
       | u1 :: l1 , nil => f (size u1) + size_minus_list f l1 l2
       | u1 :: l1, u2 :: l2 => size_minus f u1 u2 + size_minus_list f l1 l2
   end.

Lemma size_minus_unfold : forall f f1 l1 f2 l2, size_minus f (Term f1 l1) (Term f2 l2) = size_minus_list f l1 l2.
Proof.
simpl; intros f _ l1 _; induction l1 as [ | t1 l1].
intros [ | t2 l2]; apply refl_equal.
intros [ | t2 l2]; simpl; rewrite IHl1; apply refl_equal.
Qed.

Fixpoint size_common t1 t2 :=
 match t1, t2 with
 | Var _, Var _ => 1
 | Var _, Term _ _ => 0
 | Term _ _, Var _ => 0
 | Term _ l1, Term _ l2 =>
     let fix size_common_list (l1 l2 : list term) {struct l1} : nat :=
       match l1, l2 with
       | nil, _ => 0
       | _, nil => 0
       | u1 :: l1, u2 :: l2 => size_common u1 u2 + size_common_list l1 l2
       end in
       1 + size_common_list l1 l2
  end.

Fixpoint size_common_list l1 l2 :=
   match l1, l2 with
       | nil, _ => 0
       | _, nil => 0
       | u1 :: l1, u2 :: l2 => size_common u1 u2 + size_common_list l1 l2
   end.

Lemma size_common_unfold : 
  forall f1 l1 f2 l2, size_common (Term f1 l1) (Term f2 l2) = 1 + size_common_list l1 l2.
Proof.
simpl; intros _ l1 _ l2; apply f_equal.
revert l2; induction l1 as [ | t1 l1].
intros [ | t2 l2]; apply refl_equal.
intros [ | t2 l2]; simpl.
apply refl_equal.
rewrite IHl1; apply refl_equal.
Qed.

Definition eqt_meas2 f s t := size_minus f s t + size_minus f t s + size_common s t.

Fixpoint power4 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n => 4 * (power4 n)
  end.

Definition psi2 pb := 
  list_size 
    (fun st => match st with (s,t) => eqt_meas2 power4 s t end) pb.(unsolved_part) + 
  list_size
    (fun st => match st with (s,t) => eqt_meas2 power4 s t end) 
    (substitution_to_eq_list pb.(solved_part)).
 
Definition psi3 pb := 
  Fset.cardinal _
    (Fset.filter _ (fun v => negb (Oset.mem_bool OX v (map (@fst _ _) (pb.(solved_part)))))
     (vars_of_pb pb)).

Definition measure pb :=  (phi1 pb) + (psi2 pb) + (psi3 pb).

Lemma lex_le0_lt: 
   forall p1 q1 p2 q2 p3 q3,
     p1 < q1 -> p2 <= q2 -> p3 <= q3 -> p1 + p2 + p3 < q1 + q2 + q3.
Proof.
intros p1 q1 p2 q2 p3 q3 p1_lt_q1 p2_le_q2 p3_le_q3.
apply lt_le_trans with (q1 + p2 + p3).
apply plus_lt_compat_r.
apply plus_lt_compat_r.
assumption.
do 2 rewrite <- plus_assoc; apply plus_le_compat_l.
apply plus_le_compat; assumption.
Qed.

Lemma lex_le1_lt: 
  forall p1 q1  p2 q2 p3 q3,
     p1 <= q1 -> p2 < q2 -> p3 <= q3 -> p1 + p2 + p3 < q1 + q2 + q3.
Proof.
intros p1 q1 p2 q2 p3 q3 p1_le_q1 p2_lt_q2 p3_le_q3.
apply lt_le_trans with (p1 + q2 + p3).
do 2 rewrite <- plus_assoc; apply plus_lt_compat_l.
apply plus_lt_compat_r; assumption.
apply plus_le_compat; [ | assumption].
apply plus_le_compat_r; assumption.
Qed.

Lemma lex_le2_lt: 
  forall p1 q1  p2 q2 p3 q3,
     p1 <= q1 -> p2 <= q2 -> p3 < q3 -> p1 + p2 + p3 < q1 + q2 + q3.
Proof.
intros p1 q1 p2 q2 p3 q3 p1_le_q1 p2_le_q2 p3_lt_q3.
apply le_lt_trans with (q1 + q2 + p3).
apply plus_le_compat_r.
apply plus_le_compat; assumption.
apply plus_lt_compat_l; assumption.
Qed.

Lemma set_of_variables_in_eq_list_unfold :
  forall t1 t2 l, set_of_variables_in_eq_list ((t1, t2) :: l) =
                  ((variables_t FX t1 unionS variables_t FX t2) 
                    unionS set_of_variables_in_eq_list l).
Proof.
intros; apply refl_equal.
Qed.

Lemma set_of_variables_in_range_of_subst_unfold :
  forall x t sigma, set_of_variables_in_range_of_subst ((x, t) :: sigma) =
                    ((variables_t FX t) unionS (set_of_variables_in_range_of_subst sigma)).
Proof.
intros; apply refl_equal.
Qed.

Lemma substitution_to_eq_list_unfold :
  forall sigma, 
    substitution_to_eq_list sigma =
    map (fun x => (Var x, apply_subst OX sigma (Var x))) 
        ({{{domain_of_subst FX sigma}}}).
Proof.
intro sigma; apply refl_equal.
Qed.

(* Blind variable replacement, without linear variable ordering *)

Fixpoint rep_var n (sigma1 sigma2 : substitution dom symbol) :=
  match n with
    | 0 => Some (sigma1 ++ sigma2)
    | S m =>
      match sigma2 with
        | nil => Some sigma1
        | (x1, t1) :: sigma2' => 
          if x1 inS? variables_t FX t1
          then 
            match t1 with
              | Var _ => rep_var m sigma1 sigma2'
              | Term _ _ => None
            end
          else 
            let tau1 :=  
                (map (fun (xt : variable dom * term) => 
                        let (x, t) := xt in (x, apply_subst OX ((x1, t1) :: nil) t)) sigma1)  in
            let tau2 := 
                (map (fun (xt : variable dom * term) => 
                        let (x, t) := xt in (x, apply_subst OX ((x1, t1) :: nil) t)) sigma2') in
            rep_var m ((x1,t1) :: tau1) tau2
      end
  end.


Definition mgu l :=
   match decompose (measure (mk_pb nil l)) (mk_pb nil l) with
   | Some pb' => 
      let sigma := solved_part pb' in 
      let csigma := clean_subst FX sigma in
      rep_var (length csigma) nil csigma
   | None => None
   end.

Definition Inv_solved_part pb :=
  forall x, match Oset.find OX x pb.(solved_part) with 
              | Some (Var _) => is_a_solved_var x pb = true
              | _ => True
            end.

Ltac find_var_in_eq_list x :=
  repeat rewrite set_of_variables_in_eq_list_unfold;
  repeat rewrite Fset.mem_union;
  rewrite (variables_t_unfold _ (Var x)), Fset.singleton_spec, Oset.eq_bool_refl;
  repeat rewrite Bool.orb_true_r;
  apply refl_equal.

Ltac find_not_var Hx :=
  repeat rewrite set_of_variables_in_eq_list_unfold;
    repeat rewrite Fset.mem_union; 
      repeat rewrite (variables_t_unfold _ (Var _));
      repeat rewrite Fset.singleton_spec; rewrite Hx.

Ltac find_var_in_dom :=
  try apply Fset.mem_in_elements;
  unfold domain_of_subst; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.

Ltac find_var_in_subst Ht :=
  simpl fst; simpl snd; rewrite Ht, Fset.mem_union, Bool.orb_true_iff, in_variables_t_var; 
  trivial.

Lemma Inv_solved_part_init :
  forall l, Inv_solved_part (mk_pb nil l).
Proof.
intros l; unfold Inv_solved_part; simpl; trivial.
Qed.

Lemma in_vars_of_pb :
  forall x sigma l, 
    x inS vars_of_pb (mk_pb sigma l) <->
    ((exists v, exists t, (v = x \/ x inS variables_t FX t) /\ 
                          v inS domain_of_subst FX sigma /\ Oset.find OX v sigma = Some t) \/
     exists u, exists v, x inS (variables_t FX u unionS variables_t FX v) /\ In (u,v) l).
Proof.
intros x sigma l; unfold vars_of_pb.
simpl solved_part; simpl unsolved_part; 
unfold set_of_variables_in_eq_list, substitution_to_eq_list.
rewrite map_map, Fset.mem_union, Bool.orb_true_iff, 2 Fset.mem_Union; split; intros [H | H].
- right; destruct H as [s [Hs Hx]]; rewrite in_map_iff in Hs.
  destruct Hs as [[u v] [Hs H]]; subst s; exists u; exists v; split; trivial.
- destruct H as [s [Hs Hx]]; rewrite in_map_iff in Hs.
  destruct Hs as [v [Hs H]]; subst s.
  generalize (Fset.in_elements_mem _ _ _ H); clear H; intro H.
  case_eq (Oset.find OX v sigma).
  + intros t Ht; left; exists v; exists t; split; [ | split]; trivial.
    revert Hx; find_var_in_subst Ht.
  + intro Abs; apply False_rec.
    assert (H' := H); unfold domain_of_subst in H'; 
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in H'.
    destruct H' as [[_x t] [_Hx H']]; simpl in _Hx; subst _x.
    apply (Oset.find_none _ _ _ Abs _ H').
- destruct H as [v [t [H [Hv Ht]]]].
  right.
  eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ].
  + apply Fset.mem_in_elements; assumption.
  + find_var_in_subst Ht.
- destruct H as [u [v [Hx H]]].
  left; eexists; split; 
  [rewrite in_map_iff; exists (u, v); split; [apply refl_equal | ] | ]; trivial.
Qed.

Lemma var_not_in_apply_renaming_list :
  forall x y l, x <> y ->  
                x inS? set_of_variables_in_eq_list
                  (map
                     (fun uv : term * term =>
                        let (u, v) := uv in
                        (apply_subst OX ((x, Var y) :: nil) u,
                         apply_subst OX ((x, Var y) :: nil) v)) l) = false.
Proof.
intros x y l H; unfold set_of_variables_in_eq_list.
rewrite map_map, <- not_true_iff_false, Fset.mem_Union.
intro K; destruct K as [s [Hs K]]; rewrite in_map_iff in Hs.
destruct Hs as [[t1 t2] [Hs Ht]]; subst s.
rewrite Fset.mem_union, Bool.orb_true_iff in K; destruct K as [K | K].
- simpl fst in K; rewrite (var_not_in_apply_renaming_term _ _ H) in K; discriminate K.
- simpl snd in K; rewrite (var_not_in_apply_renaming_term _ _ H) in K; discriminate K.
Qed.

Lemma var_not_in_apply_renaming_range_of_subst :
  forall x y sigma, x <> y ->  
                    (x
                       inS? set_of_variables_in_range_of_subst
                       (map
                          (fun vv_sigma : variable dom * term =>
                             let (v, v_sigma) := vv_sigma in
                             (v, apply_subst OX ((x, Var y) :: nil) v_sigma))
                          sigma)) = false.
Proof.
intros x y sigma H; unfold set_of_variables_in_range_of_subst.
rewrite map_map, <- not_true_iff_false, Fset.mem_Union.
intro K; destruct K as [s [Hs K]]; rewrite in_map_iff in Hs.
destruct Hs as [[x1 t2] [Hs Ht]]; subst s.
simpl snd in K; rewrite (var_not_in_apply_renaming_term _ _ H) in K; discriminate K.
Qed.

Lemma in_apply_renaming_term :
  forall x y z t, 
    z inS (variables_t FX (apply_subst OX ((x, Var (symbol := symbol) y) :: nil) t)) ->
    (z inS (variables_t FX t) \/ z = y).
Proof.
intros x y z t; pattern t; apply term_rec3; clear t.
- intros v; simpl apply_subst; case_eq (Oset.eq_bool OX v x); intro Hv.
  + intro Hz; rewrite in_variables_t_var in Hz; right; apply sym_eq; trivial.
  + intro; left; assumption.
- intros f l IHl; simpl apply_subst; 
  rewrite 2 (variables_t_unfold _ (Term _ _)), map_map, 2 Fset.mem_Union.
  intros [s [Hs Ks]]; rewrite in_map_iff in Hs.
  destruct Hs as [t [Hs Ht]]; subst s.
  destruct (IHl _ Ht Ks) as [Hz | Hz]; [ | right; assumption].
  left; exists (variables_t FX t); split; trivial.
  rewrite in_map_iff; exists t; split; trivial.
Qed.

Lemma in_apply_renaming_eq_list : 
 forall x y z l,    
   z inS (set_of_variables_in_eq_list
            (map
               (fun uv => match uv with
                              | (u, v) => 
                                (apply_subst OX ((x, Var y) :: nil) u,
                                 apply_subst OX ((x, Var y) :: nil) v)
                          end) l)) ->
  (z inS (set_of_variables_in_eq_list l) \/ z = y).
 Proof.
 intros x y z l Hz.
 unfold set_of_variables_in_eq_list in *; rewrite map_map, Fset.mem_Union in Hz.
 destruct Hz as [s [Hs Hz]]; rewrite in_map_iff in Hs.
 destruct Hs as [[t1 t2] [Hs Ht]]; subst s.
 simpl fst in Hz; simpl snd in Hz.
 rewrite Fset.mem_union, Bool.orb_true_iff in Hz; 
   destruct Hz as [Hz | Hz]; (destruct (in_apply_renaming_term _ _ _ _ Hz) as [Kz | Kz]).
 - left; rewrite Fset.mem_Union; exists (variables_t FX t1 unionS variables_t FX t2); split.
   + rewrite in_map_iff; exists (t1, t2); split; trivial.
   + rewrite Fset.mem_union, Kz; apply refl_equal.
 - right; assumption.
 - left; rewrite Fset.mem_Union; exists (variables_t FX t1 unionS variables_t FX t2); split.
   + rewrite in_map_iff; exists (t1, t2); split; trivial.
   + rewrite Fset.mem_union, Kz, Bool.orb_true_r; apply refl_equal.
 - right; assumption.
Qed.

Lemma in_apply_renaming_subst :
   forall x y z sigma,
     z inS (set_of_variables_in_eq_list 
              (substitution_to_eq_list          
                 (map
                    (fun zt : variable dom * term =>
                       match zt with 
                         | (z, t) => (z, apply_subst OX ((x, Var y) :: nil) t)
                       end) sigma))) ->
     (z inS set_of_variables_in_eq_list (substitution_to_eq_list sigma) \/ z = y).
Proof.
 intros x y z sigma Hz.
 unfold set_of_variables_in_eq_list in *.
 rewrite Fset.mem_Union in Hz.
 destruct Hz as [s [Hs Hz]]; rewrite in_map_iff in Hs.
 destruct Hs as [[t1 t2] [Hs Hu]].
 unfold substitution_to_eq_list in *.
 rewrite map_map.
 rewrite in_map_iff in Hu; destruct Hu as [v [Hu Hv]].
 rewrite (Fset.elements_spec1 _ _ _ (domain_of_subst_inv _ _ _)) in Hv.
 injection Hu; clear Hu; do 2 intro; subst t1 t2.
 simpl fst in Hs; simpl snd in Hs; subst s.
 rewrite Fset.mem_union, Bool.orb_true_iff in Hz.
 destruct Hz as [Hz | Hz].
 - rewrite in_variables_t_var in Hz; subst z.
   left; rewrite Fset.mem_Union.
   eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ].
   + assumption.
   + simpl fst; find_var_in_eq_list v.
 - case_eq (Oset.find OX v sigma).
   + intros u Hu.
     rewrite (Oset.find_some_map _ _ _ _ Hu) in Hz.
     destruct (in_apply_renaming_term _ _ _ _ Hz) as [Jz | Jz].
     * left; rewrite Fset.mem_Union.
       eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ]; trivial.
       find_var_in_subst Hu; right; assumption.
     * right; assumption.
   + intro Hu; apply False_rec.
     generalize (Fset.in_elements_mem _ _ _ Hv).
     unfold domain_of_subst; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff.
     apply (Oset.find_none_alt OX _ _ Hu).
 Qed.

 Lemma in_apply_renaming_range_of_subst :
   forall x y z sigma,
     z inS set_of_variables_in_range_of_subst
           (map
              (fun zt : variable dom * term =>
                 match zt with 
                   | (z, t) => (z, apply_subst OX ((x, Var y) :: nil) t)
                 end) sigma) ->
     (z inS set_of_variables_in_range_of_subst sigma \/ z = y).
 Proof.
 intros x y z sigma Hz.
 unfold set_of_variables_in_range_of_subst in *; rewrite map_map, Fset.mem_Union in Hz.
 destruct Hz as [s [Hs Hz]]; rewrite in_map_iff in Hs.
 destruct Hs as [[x1 t2] [Hs Ht]]; subst s.
 simpl snd in Hz.
 destruct (in_apply_renaming_term _ _ _ _ Hz) as [Kz | Kz].
 - left; rewrite Fset.mem_Union; exists (variables_t FX t2); split; trivial.
   rewrite in_map_iff; exists (x1, t2); split; trivial.
 - right; assumption.
 Qed.

 Lemma in_apply_renaming_term_alt :
   forall x y z t, 
     z <> x -> z inS (variables_t FX t) ->
     z inS (variables_t (symbol := symbol) FX (apply_subst OX ((x, Var y) :: nil) t)).
 Proof.
 intros x y z t Hz; pattern t; apply term_rec3; clear t.
 - intros v; simpl apply_subst; case_eq (Oset.eq_bool OX v x); intro Hv.
   + rewrite Oset.eq_bool_true_iff in Hv; subst v.
     rewrite in_variables_t_var; intro; subst; apply False_rec; apply Hz; trivial.
   + exact (fun h => h).
 - intros f l IHl; simpl apply_subst; rewrite 2 (variables_t_unfold _ (Term _ _)).
   rewrite map_map, 2 Fset.mem_Union.
   intros [s [Hs Ks]]; rewrite in_map_iff in Hs.
   destruct Hs as [t [Hs Ht]]; subst s.
   eexists; split; [rewrite in_map_iff; exists t; split; [apply refl_equal | ] | ]; trivial.
   apply IHl; trivial.
 Qed.

 Lemma in_apply_renaming_eq_list_alt : 
   forall x y z l, z <> x ->  z inS (set_of_variables_in_eq_list l) ->
                   z inS (set_of_variables_in_eq_list
                            (map
                               (fun uv => match uv with
                                            | (u, v) => 
                                              (apply_subst OX ((x, Var y) :: nil) u,
                                               apply_subst OX ((x, Var y) :: nil) v)
                                          end) l)).
 Proof.
 intros x y z l Hx Hz.
 unfold set_of_variables_in_eq_list in *; rewrite Fset.mem_Union in Hz.
 rewrite map_map, Fset.mem_Union.
 destruct Hz as [s [Hs Hz]]; rewrite in_map_iff in Hs.
 destruct Hs as [[t1 t2] [Hs Ht]]; subst s.
 simpl fst in Hz; simpl snd in Hz.
 rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz]. 
 - eexists; split; [rewrite in_map_iff; exists (t1, t2); split; [apply refl_equal | ] | ].
   + assumption.
   + simpl fst; simpl snd; rewrite Fset.mem_union, (in_apply_renaming_term_alt _ _ Hx Hz).
     apply refl_equal.
 - eexists; split; [rewrite in_map_iff; exists (t1, t2); split; [apply refl_equal | ] | ].
   + assumption.
   + simpl fst; simpl snd; rewrite Fset.mem_union, (in_apply_renaming_term_alt _ _ Hx Hz).
     rewrite Bool.orb_true_r; apply refl_equal.
 Qed.

Lemma combine_unfold : 
 forall A (l1 l2 : list A) l, combine l l1 l2 = combine nil l1 l2 ++ l.
Proof.
fix combine_unfold 3.
intros B l1 l2 l; case l1; clear l1.
apply refl_equal.
intros a1 l1; case l2; clear l2; simpl.
apply refl_equal.
intros a2 l2.
rewrite (combine_unfold B l1 l2 ((a1,a2) :: l)).
rewrite (combine_unfold B l1 l2 ((a1,a2) :: nil)).
rewrite <- ass_app; apply refl_equal.
Qed.

Lemma vars_of_pb_inv :
  forall pb,
    match decomposition_step pb with
      | Normal pb' => vars_of_pb pb' subS vars_of_pb pb
      | _ => True
    end.
Proof.
  unfold decomposition_step.
  intros [sigma [ | [s t] l]]; 
    [exact I | unfold is_a_solved_var; simpl solved_part; simpl unsolved_part].
  case_eq (Oset.eq_bool (OT OX OF) s t); intro Hst.
  - (* 1/2 trivial equation *)
    rewrite Fset.subset_spec; intro x; rewrite 2 in_vars_of_pb.
    intros [H | H]; [left; assumption | right].
   destruct H as [u [v [Hx H]]].
   exists u; exists v; split; [ | right]; trivial.
 - (* 1/1 *)
   rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in Hst.
   destruct s as [x | f l1]; destruct t as [y | g l2].
   (* 1/4 Coalesce *)
   + assert (H : x <> y).
     {
       intro; subst y; apply Hst; apply refl_equal.
     }
     case_eq (Oset.find OX x sigma); [ intros x_val x_sigma | intro x_sigma].
     * (* 1/5 *)
       rewrite (Oset.find_some_map _ _ _ _ x_sigma).
       rewrite Fset.subset_spec; intro z.
       {
         case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
         - (* 1/6 *)
           rewrite Oset.eq_bool_true_iff in z_eq_x; subst z; intros _.
           rewrite in_vars_of_pb; right.
           eexists; eexists; split; [ | left; apply refl_equal].
           find_var_in_eq_list x.
         - case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
           + rewrite Oset.eq_bool_true_iff in z_eq_y; subst z; intros _.
             rewrite in_vars_of_pb; right.
             eexists; eexists; split; [ | left; apply refl_equal].
             find_var_in_eq_list y.
           + rewrite in_vars_of_pb; intros [Hz | Hz].
             * destruct Hz as [v [_t [Hz [Hv Kv]]]].
               rewrite domain_of_subst_unfold, Fset.add_spec, 
                 (Fset.mem_eq_2 _ _ _ (domain_of_subst_inv _ _ _)) in Hv.
               {
                 case_eq (Oset.eq_bool OX v x); intro Jv.
                 - rewrite Oset.eq_bool_true_iff in Jv; subst v.
                   simpl Oset.find in Kv; rewrite Oset.eq_bool_refl in Kv.
                   injection Kv; clear Kv; intro; subst _t.
                   destruct Hz as [Hz | Hz]; 
                     [subst z; rewrite Oset.eq_bool_refl in z_diff_x; discriminate z_diff_x | ].
                   rewrite in_vars_of_pb; right.
                   eexists; eexists; split; [ | left; apply refl_equal].
                   rewrite in_variables_t_var in Hz; subst z; find_var_in_eq_list y.
                 - rewrite Jv, Bool.orb_false_l in Hv.
                   simpl in Kv; rewrite Jv in Kv.
                   case_eq (Oset.find OX v sigma); [intros v_val v_sigma | intro v_sigma].
                   + rewrite (Oset.find_some_map _ _ _ _ v_sigma) in Kv.
                     injection Kv; clear Kv; intro; subst _t.
                     destruct Hz as [Hz | Hz].
                     * subst z; rewrite in_vars_of_pb.
                       left; exists v; exists v_val; repeat split; trivial.
                       left; trivial.
                     * {
                         destruct (in_apply_renaming_term _ _ _ _ Hz) as [Jz | Jz].
                         - rewrite in_vars_of_pb; left.
                           exists v; exists v_val; repeat split; trivial.
                           right; trivial.
                         - subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
                       } 
                   + rewrite (Oset.find_none_map _ _ _ _ v_sigma) in Kv; discriminate Kv.
               }
             * destruct Hz as [u [v [Hz K]]].
               {
                 simpl in K; destruct K as [K | K].
                 - injection K; clear K; do 2 intro; subst u v.
                   revert Hz; find_not_var z_diff_y; rewrite Bool.orb_false_l; intro Hz.
                   destruct (in_apply_renaming_term _ _ _ _ Hz) as [Jz | Jz].
                   + rewrite in_vars_of_pb; left.
                     exists x; exists x_val; repeat split; trivial.
                     * right; trivial.
                     * unfold domain_of_subst; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff.
                       rewrite in_map_iff; exists (x, x_val); split; trivial.
                       apply (Oset.find_some _ _ _ x_sigma).
                   + subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
                 - rewrite in_vars_of_pb.
                   destruct (in_apply_renaming_eq_list x y z l) as [H1 | H1].
                   + unfold set_of_variables_in_eq_list; rewrite Fset.mem_Union.
                     eexists; split; [ | apply Hz].
                     rewrite in_map_iff; exists (u, v); split; trivial.
                   + right; unfold set_of_variables_in_eq_list in H1; rewrite Fset.mem_Union in H1.
                     destruct H1 as [s [Hs H1]]; rewrite in_map_iff in Hs.
                     destruct Hs as [[u1 v1] [Hs H2]]; subst s.
                     exists u1; exists v1; split; [ | right]; trivial.
                   + subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
               }
       }
     * rewrite (Oset.find_none_map _ _ _ _ x_sigma).
       rewrite Fset.subset_spec; intro z.
       {
         case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
         - (* 1/5 *)
           rewrite Oset.eq_bool_true_iff in z_eq_x; subst z; intros _.
           rewrite in_vars_of_pb; right.
           eexists; eexists; split; [ | left; apply refl_equal].
           find_var_in_eq_list x.
         - case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
           + rewrite Oset.eq_bool_true_iff in z_eq_y; subst z; intros _.
             rewrite in_vars_of_pb; right.
             eexists; eexists; split; [ | left; apply refl_equal].
             find_var_in_eq_list y.
           + rewrite in_vars_of_pb; intros [Hz | Hz].
             * destruct Hz as [v [_t [Hz [Hv Kv]]]].
               rewrite domain_of_subst_unfold, Fset.add_spec, 
                 (Fset.mem_eq_2 _ _ _ (domain_of_subst_inv _ _ _)) in Hv.
               {
                 case_eq (Oset.eq_bool OX v x); intro Jv.
                 - rewrite Oset.eq_bool_true_iff in Jv; subst v.
                   simpl Oset.find in Kv; rewrite Oset.eq_bool_refl in Kv.
                   injection Kv; clear Kv; intro; subst _t.
                   destruct Hz as [Hz | Hz]; 
                     [subst z; rewrite Oset.eq_bool_refl in z_diff_x; discriminate z_diff_x | ].
                   rewrite in_vars_of_pb; right.
                   eexists; eexists; split; [ | left; apply refl_equal].
                   rewrite in_variables_t_var in Hz; subst z; find_var_in_eq_list y.
                 - rewrite Jv, Bool.orb_false_l in Hv.
                   simpl in Kv; rewrite Jv in Kv.
                   case_eq (Oset.find OX v sigma); [intros v_val v_sigma | intro v_sigma].
                   + rewrite (Oset.find_some_map _ _ _ _ v_sigma) in Kv.
                     injection Kv; clear Kv; intro; subst _t.
                     destruct Hz as [Hz | Hz].
                     * subst z; rewrite in_vars_of_pb.
                       left; exists v; exists v_val; repeat split; trivial.
                       left; trivial.
                     * {
                         destruct (in_apply_renaming_term _ _ _ _ Hz) as [Jz | Jz].
                         - rewrite in_vars_of_pb; left.
                           exists v; exists v_val; repeat split; trivial.
                           right; trivial.
                         - subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
                       } 
                   + rewrite (Oset.find_none_map _ _ _ _ v_sigma) in Kv; discriminate Kv.
               }
             * destruct Hz as [u [v [Hz K]]].
               rewrite in_vars_of_pb.
               {
                 destruct (in_apply_renaming_eq_list x y z l) as [H1 | H1].
                 - unfold set_of_variables_in_eq_list; rewrite Fset.mem_Union.
                   eexists; split; [ | apply Hz].
                   rewrite in_map_iff; exists (u, v); split; trivial.
                 - right; unfold set_of_variables_in_eq_list in H1; rewrite Fset.mem_Union in H1.
                   destruct H1 as [s [Hs H1]]; rewrite in_map_iff in Hs.
                   destruct Hs as [[u1 v1] [Hs H2]]; subst s.
                   exists u1; exists v1; split; [ | right]; trivial.
                 - subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
               }
       }
   + case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
     * destruct x_val as [ | f l1]; [trivial | ].
       {
         case_eq (Oset.compare Onat (size (Term g l2)) (size (Term f l1))); intro L.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz]; [left; assumption | ].
           destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
           + injection H; clear H; do 2 intro; subst u v.
             rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
             * {
                 left; exists x; exists (Term f l1); repeat split; trivial.
                 - right; assumption.
                 - unfold domain_of_subst.
                   rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                   exists (x, (Term f l1)); split; trivial.
                   apply (Oset.find_some _ _ _ x_sigma).
               }
             * right; exists (Var x); exists (Term g l2); split; [ | left; trivial].
               rewrite Fset.mem_union, Hz, Bool.orb_true_r.
               apply refl_equal.
           + right; exists u; exists v; split; [ | right]; trivial.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz].
           + destruct Hz as [v [t [Hv [Kv Jv]]]].
             rewrite domain_of_subst_unfold, Fset.add_spec in Kv.
             simpl Oset.find in Jv.
             case_eq (Oset.eq_bool OX v x); intro Hx; rewrite Hx in Kv, Jv.
             * rewrite Oset.eq_bool_true_iff in Hx; subst v.
               injection Jv; clear Jv; intro; subst t.
               {
                 destruct Hv as [Hv | Hv].
                 - subst z; left.
                   exists x; exists (Term f l1); repeat split; trivial.
                   + left; trivial.
                   + unfold domain_of_subst.
                     rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                     exists (x, (Term f l1)); split; trivial.
                     apply (Oset.find_some _ _ _ x_sigma).
                 - right; eexists; eexists; split; [ | left; apply refl_equal].
                   rewrite Fset.mem_union, Hv, Bool.orb_true_r; apply refl_equal.
               }
             * left; exists v; exists t; repeat split; trivial.
           + destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
             * injection H; clear H; do 2 intro; subst u v.
               {
                 rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
                 - left; exists x; exists (Term f l1); repeat split; trivial.
                   + right; assumption.
                   + unfold domain_of_subst.
                     rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                     exists (x, (Term f l1)); split; trivial.
                     apply (Oset.find_some _ _ _ x_sigma).
                 - right; exists (Var x); exists (Term g l2); split; [ | left; trivial].
                   rewrite Fset.mem_union, Hz, Bool.orb_true_r.
                   apply refl_equal.
               } 
             * right; exists u; exists v; split; [ | right]; trivial.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz]; [left; trivial | ].
           destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
           + injection H; clear H; do 2 intro; subst u v.
             rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
             * {
                 left; exists x; exists (Term f l1); repeat split; trivial.
                 - right; assumption.
                 - unfold domain_of_subst.
                   rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                   exists (x, (Term f l1)); split; trivial.
                   apply (Oset.find_some _ _ _ x_sigma).
               }
             * right; exists (Var x); exists (Term g l2); split; [ | left; trivial].
               rewrite Fset.mem_union, Hz, Bool.orb_true_r.
               apply refl_equal.
           + right; exists u; exists v; split; [ | right]; trivial.
       }
     * rewrite Fset.subset_spec; intro z.
       {
         rewrite in_vars_of_pb; intros [Hz | Hz].
         - destruct Hz as [v [_t [Hz [Hv Kv]]]].
           rewrite domain_of_subst_unfold, Fset.add_spec in Hv. 
           case_eq (Oset.eq_bool OX v x); intro Jv.
           + rewrite Oset.eq_bool_true_iff in Jv; subst v.
             simpl Oset.find in Kv; rewrite Oset.eq_bool_refl in Kv.
             injection Kv; clear Kv; intro; subst _t.
             destruct Hz as [Hz | Hz].
             * rewrite in_vars_of_pb; right.
               eexists; eexists; split; [ | left; apply refl_equal].
               subst z; find_var_in_eq_list x.
             * rewrite in_vars_of_pb; right.
               eexists; eexists; split; [ | left; apply refl_equal].
               rewrite Fset.mem_union, Hz, Bool.orb_true_r; apply refl_equal.
           + rewrite Jv, Bool.orb_false_l in Hv.
             simpl in Kv; rewrite Jv in Kv.
             destruct Hz as [Hz | Hz].
             * subst v; rewrite in_vars_of_pb; left.
               exists z; exists _t; repeat split; trivial.
               left; trivial.
             * rewrite in_vars_of_pb; left.
               exists v; exists _t; repeat split; trivial.
               right; trivial.
         - destruct Hz as [u [v [Hz K]]].
           rewrite in_vars_of_pb; right.
           exists u; exists v; split; [ | right]; trivial.
       }
   + case_eq (Oset.find OX y sigma); [intros y_val y_sigma | intro y_sigma].
     * destruct y_val as [ | g l2]; [trivial | ].
       {
         case_eq (Oset.compare Onat (size (Term f l1)) (size (Term g l2))); intro L.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz]; [left; assumption | ].
           destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
           + injection H; clear H; do 2 intro; subst u v.
             rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
             * {
                 left; exists y; exists (Term g l2); repeat split; trivial.
                 - right; assumption.
                 - unfold domain_of_subst.
                   rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                   exists (y, (Term g l2)); split; trivial.
                   apply (Oset.find_some _ _ _ y_sigma).
               }
             * right; exists (Term f l1); exists (Var y); split; [ | left; trivial].
               rewrite Fset.mem_union, Hz; apply refl_equal.
           + right; exists u; exists v; split; [ | right]; trivial.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz].
           + destruct Hz as [v [t [Hv [Kv Jv]]]].
             rewrite domain_of_subst_unfold, Fset.add_spec in Kv.
             simpl Oset.find in Jv.
             case_eq (Oset.eq_bool OX v y); intro Hy; rewrite Hy in Kv, Jv.
             * rewrite Oset.eq_bool_true_iff in Hy; subst v.
               injection Jv; clear Jv; intro; subst t.
               {
                 destruct Hv as [Hv | Hv].
                 - subst z; left.
                   exists y; exists (Term g l2); repeat split; trivial.
                   + left; trivial.
                   + unfold domain_of_subst.
                     rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                     exists (y, (Term g l2)); split; trivial.
                     apply (Oset.find_some _ _ _ y_sigma).
                 - right; eexists; eexists; split; [ | left; apply refl_equal].
                   rewrite Fset.mem_union, Hv; apply refl_equal.
               }
             * left; exists v; exists t; repeat split; trivial.
           + destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
             * injection H; clear H; do 2 intro; subst u v.
               {
                 rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
                 - left; exists y; exists (Term g l2); repeat split; trivial.
                   + right; assumption.
                   + unfold domain_of_subst.
                     rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                     exists (y, (Term g l2)); split; trivial.
                     apply (Oset.find_some _ _ _ y_sigma).
                 - right; exists (Term f l1); exists (Var y); split; [ | left; trivial].
                   rewrite Fset.mem_union, Hz; apply refl_equal.
               } 
             * right; exists u; exists v; split; [ | right]; trivial.
         - rewrite Fset.subset_spec; intro z.
           rewrite 2 in_vars_of_pb; intros [Hz | Hz]; [left; trivial | ].
           destruct Hz as [u [v [Hz H]]]; simpl in H; destruct H as [H | H].
           + injection H; clear H; do 2 intro; subst u v.
             rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
             * {
                 left; exists y; exists (Term g l2); repeat split; trivial.
                 - right; assumption.
                 - unfold domain_of_subst.
                   rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                   exists (y, (Term g l2)); split; trivial.
                   apply (Oset.find_some _ _ _ y_sigma).
               }
             * right; exists (Term f l1); exists (Var y); split; [ | left; trivial].
               rewrite Fset.mem_union, Hz; apply refl_equal.
           + right; exists u; exists v; split; [ | right]; trivial.
       }
     * rewrite Fset.subset_spec; intro z.
       {
         rewrite in_vars_of_pb; intros [Hz | Hz].
         - destruct Hz as [v [_t [Hz [Hv Kv]]]].
           rewrite domain_of_subst_unfold, Fset.add_spec in Hv. 
           case_eq (Oset.eq_bool OX v y); intro Jv.
           + rewrite Oset.eq_bool_true_iff in Jv; subst v.
             simpl Oset.find in Kv; rewrite Oset.eq_bool_refl in Kv.
             injection Kv; clear Kv; intro; subst _t.
             destruct Hz as [Hz | Hz].
             * rewrite in_vars_of_pb; right.
               eexists; eexists; split; [ | left; apply refl_equal].
               subst z; find_var_in_eq_list y.
             * rewrite in_vars_of_pb; right.
               eexists; eexists; split; [ | left; apply refl_equal].
               rewrite Fset.mem_union, Hz; apply refl_equal.
           + rewrite Jv, Bool.orb_false_l in Hv.
             simpl in Kv; rewrite Jv in Kv.
             destruct Hz as [Hz | Hz].
             * subst v; rewrite in_vars_of_pb; left.
               exists z; exists _t; repeat split; trivial.
               left; trivial.
             * rewrite in_vars_of_pb; left.
               exists v; exists _t; repeat split; trivial.
               right; trivial.
         - destruct Hz as [u [v [Hz K]]].
           rewrite in_vars_of_pb; right.
           exists u; exists v; split; [ | right]; trivial.
       }
   + case_eq (Oset.eq_bool OF f g); intro Hf; [ | trivial].
     case_eq (Oset.eq_bool Onat (length l1) (length l2)); intro L; [ | trivial].
     rewrite Fset.subset_spec; intro z.
     rewrite 2 in_vars_of_pb.
     intros [Hz | Hz]; [left; assumption | right].
     destruct Hz as [u [v [Hz H]]].
     rewrite Oset.eq_bool_true_iff in L.
     rewrite combine_unfold in H; destruct (in_app_or _ _ _ H) as [H1 | H1];
     [ | exists u; exists v; split; [ | right]; trivial].
     clear H; eexists; eexists; split; [ | left; apply refl_equal].
     rewrite 2 (variables_t_unfold _ (Term _ _)).
     clear Hst; revert l2 L Hz H1; 
     induction l1 as [ | t1 l1]; intros [ | t2 l2] L Hz H1; try discriminate L.
     * contradiction H1.
     * simpl in H1; rewrite combine_unfold in H1.
       simpl in L; injection L; clear L; intro L.
       rewrite 2 (map_unfold _ (_ :: _)), 2 (Fset.Union_unfold _ (_ :: _)).
       rewrite 3 Fset.mem_union. 
       {
         destruct (in_app_or _ _ _ H1) as [H2 | H2].
         - assert (IH := IHl1 _ L Hz H2).
           rewrite Fset.mem_union, Bool.orb_true_iff in IH.
           destruct IH as [IH | IH]; rewrite IH; repeat rewrite Bool.orb_true_r; trivial.
         - simpl in H2; destruct H2 as [H2 | H2]; [ | contradiction H2].
           injection H2; clear H2; do 2 intro; subst t1 t2.
           rewrite Fset.mem_union, Bool.orb_true_iff in Hz.
           destruct Hz as [Hz | Hz]; rewrite Hz; repeat rewrite Bool.orb_true_r; trivial.
       }
Qed.

Lemma is_a_solved_var_inv :
  forall pb,
  match decomposition_step pb with
   | Normal pb' => forall x, is_a_solved_var x pb = true -> is_a_solved_var x pb' = true
   | _ => True
   end.
Proof.
intro pb.
unfold decomposition_step.
destruct pb as [sigma [ | [s t] l]]; 
  [exact I | unfold is_a_solved_var; simpl solved_part; simpl unsolved_part].
case_eq (Oset.eq_bool (OT OX OF) s t); intro Hst.
- (* 1/2 trivial equation *)
  intro x; simpl solved_part; simpl unsolved_part.
  case_eq (Oset.find OX x sigma); [ | exact (fun _ h => h)].
  intros x_val x_sigma.
  rewrite 2 Bool.andb_true_iff; intros [H1 H2]; split; [ | exact H2].
  rewrite negb_true_iff, <- not_true_iff_false in H1.
  rewrite negb_true_iff, <- not_true_iff_false; intro H3; apply H1.
  rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, H3, Bool.orb_true_r.
  apply refl_equal.
- rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in Hst.
(* 1/1 *)
  destruct s as [x | f l1]; destruct t as [y | g l2].
  (* 1/4 Coalesce *)
  + assert (H : x <> y).
    {
      intro; subst y; apply Hst; apply refl_equal.
    }
    case_eq (Oset.find OX x sigma); [ intros x_val x_sigma | intro x_sigma].
    * (* 1/5 *)
      rewrite (Oset.find_some_map _ _ _ _ x_sigma); simpl solved_part; simpl unsolved_part.
      intro z; simpl.
      {
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        - (* 1/6 *)
          rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          rewrite x_sigma.
          rewrite Bool.andb_true_iff; intros [Hx _].
          rewrite negb_true_iff, <- not_true_iff_false in Hx.
          apply False_rec; apply Hx; find_var_in_eq_list x.
        - case_eq (Oset.find OX z sigma);
          [ intros z_val z_sigma | intros _ Abs; discriminate Abs].
          rewrite (Oset.find_some_map _ _ _ _ z_sigma).
          case_eq (Oset.eq_bool OX z y); intro Hy.
          + rewrite Oset.eq_bool_true_iff in Hy; subst z.
            rewrite Bool.andb_true_iff, negb_true_iff, <- not_true_iff_false; intros [Ky _].
            apply False_rec; apply Ky; find_var_in_eq_list y.
          + find_not_var z_diff_x; find_not_var Hy; rewrite 2 Bool.orb_false_l.
            rewrite 2 Bool.andb_true_iff, 4 negb_true_iff, <- 4 not_true_iff_false.
            intros [Hz Kz]; split; intro K.
            * {
                rewrite Bool.orb_true_iff in K; destruct K as [K | K].
                - destruct (in_apply_renaming_term _ _ _ _ K) as [J | J].
                  + apply Kz.
                    unfold set_of_variables_in_range_of_subst.
                    rewrite Fset.mem_Union.
                    eexists; split; 
                    [rewrite in_map_iff; exists (x, x_val); split; [apply refl_equal | ] | ].
                    * apply (Oset.find_some _ _ _ x_sigma).
                    * apply J.
                  + subst z; rewrite Oset.eq_bool_refl in Hy; discriminate Hy.
                - destruct (in_apply_renaming_eq_list _ _ _ _ K) as [J | J].
                  + apply Hz; assumption.
                  + subst z; rewrite Oset.eq_bool_refl in Hy; discriminate Hy.
              }
            * unfold set_of_variables_in_range_of_subst in K.
              rewrite map_unfold, Fset.Union_unfold, Fset.mem_union, Bool.orb_true_iff in K.
              {
                destruct K as [J | J].
                - simpl in J; rewrite Fset.singleton_spec, Hy in J.
                  discriminate J.
                - destruct (in_apply_renaming_range_of_subst x y z sigma J) as [L | L].
                  + apply Kz; apply L.
                  + subst z; rewrite Oset.eq_bool_refl in Hy; discriminate Hy.
              }
      }
    * rewrite (Oset.find_none_map _ _ _ _ x_sigma).
      intro z; simpl solved_part; simpl unsolved_part; simpl Oset.find.
      {
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        - rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          rewrite x_sigma; intro Abs; discriminate Abs.
        - case_eq (Oset.find OX z sigma); [intros z_val z_sigma | intro z_sigma].
          + rewrite (Oset.find_some_map _ _ _ _ z_sigma).
            case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
            * rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
              rewrite Bool.andb_true_iff, negb_true_iff, <- not_true_iff_false; intros [Ky _].
              apply False_rec; apply Ky; find_var_in_eq_list y.
            * find_not_var z_diff_x; find_not_var z_diff_y; rewrite Bool.orb_false_l.
              rewrite 2 Bool.andb_true_iff, 4 negb_true_iff, <- 4 not_true_iff_false.
              {
                intros [Hz Kz]; split; intro K.
                - destruct (in_apply_renaming_eq_list _ _ _ _ K) as [J | J].
                  + apply Hz; assumption.
                  + subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
                - unfold set_of_variables_in_range_of_subst in K.
                  rewrite map_unfold, Fset.Union_unfold, Fset.mem_union, Bool.orb_true_iff in K.
                  destruct K as [K | K].
                  + simpl snd in K; rewrite in_variables_t_var in K; subst z.
                    rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
                  + destruct (in_apply_renaming_range_of_subst _ _ _ _ K) as [K1 | K1].
                    * apply Kz; assumption.
                    * subst z; rewrite Oset.eq_bool_refl in z_diff_y; discriminate z_diff_y.
              }
          + intro Abs; discriminate Abs.
      }
  + case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
    * destruct x_val as [ | f l1]; [trivial | ].
      {
        case_eq (Oset.compare Onat (size (Term g l2)) (size (Term f l1))); intro L.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; rewrite z_sigma.
          rewrite 2 Bool.andb_true_iff; intros [Hz Kz]; split; [ | assumption].
          rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
            Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
          rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
          rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
          rewrite Fset.mem_union, Hz2, Bool.orb_false_r.
          rewrite negb_true_iff, <- not_true_iff_false in Kz.
          rewrite negb_true_iff, <- not_true_iff_false; intro H.
          apply Kz; unfold set_of_variables_in_range_of_subst.
          rewrite Fset.mem_Union; eexists; split; 
          [rewrite in_map_iff; exists (x, Term f l1); split; [apply refl_equal | ] | ].
          + apply (Oset.find_some _ _ _ x_sigma).
          + apply H.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; simpl Oset.find.
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
          + rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
            rewrite x_sigma in z_sigma; injection z_sigma; intro; subst z_val; clear z_sigma.
            rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
            rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
              Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
            rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
            rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
            rewrite Fset.mem_union, Hz2, Bool.orb_false_r.
            rewrite negb_true_iff in Kz.
            split; rewrite negb_true_iff, <- not_true_iff_false; intro H.
            * rewrite <- not_true_iff_false in Kz.
              apply Kz; unfold set_of_variables_in_range_of_subst.
              {
                rewrite Fset.mem_Union; eexists; split; 
                [rewrite in_map_iff; exists (x, Term f l1); split; [apply refl_equal | ] | ].
                - apply (Oset.find_some _ _ _ x_sigma).
                - apply H.
              }
            * unfold set_of_variables_in_range_of_subst in H.
              rewrite map_unfold, Fset.Union_unfold, Fset.mem_union in H.
              simpl snd in H; rewrite Hz2, Bool.orb_false_l in H.
              unfold set_of_variables_in_range_of_subst in Kz.
              rewrite H in Kz; discriminate Kz.
          + rewrite z_sigma.
            rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
            rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
              Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
            rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
            rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
            rewrite Fset.mem_union, Hz2, Bool.orb_false_r.
            rewrite negb_true_iff in Kz.
            split; rewrite negb_true_iff, <- not_true_iff_false; intro H.
            * rewrite <- not_true_iff_false in Kz.
              apply Kz; unfold set_of_variables_in_range_of_subst.
              {
                rewrite Fset.mem_Union; eexists; split; 
                [rewrite in_map_iff; exists (x, Term f l1); split; [apply refl_equal | ] | ].
                - apply (Oset.find_some _ _ _ x_sigma).
                - simpl snd; apply H.
              }
            * unfold set_of_variables_in_range_of_subst in H.
              rewrite map_unfold, Fset.Union_unfold, Fset.mem_union in H.
              simpl snd in H; rewrite Hz2, Bool.orb_false_l in H.
              unfold set_of_variables_in_range_of_subst in Kz.
              rewrite H in Kz; discriminate Kz.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; rewrite z_sigma.
          rewrite 2 Bool.andb_true_iff; intros [Hz Kz]; split; [ | assumption].
          rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
            Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
          rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
          rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
          rewrite Fset.mem_union, Hz2, Bool.orb_false_r.
          rewrite negb_true_iff, <- not_true_iff_false in Kz.
          rewrite negb_true_iff, <- not_true_iff_false; intro H.
          apply Kz; unfold set_of_variables_in_range_of_subst.
          rewrite Fset.mem_Union; eexists; split; 
          [rewrite in_map_iff; exists (x, Term f l1); split; [apply refl_equal | ] | ].
          + apply (Oset.find_some _ _ _ x_sigma).
          + apply H.
      }
    * intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
      intros z_val z_sigma; simpl solved_part; simpl unsolved_part.
      simpl Oset.find; rewrite z_sigma.
      case_eq (Oset.eq_bool OX z x); 
        [ intro z_eq_x; rewrite Oset.eq_bool_true_iff in z_eq_x; subst z; 
          rewrite x_sigma in z_sigma; discriminate z_sigma
        | intro z_diff_x].
      rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
      rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
        Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
      rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
      rewrite Hz'; split; [trivial | ].
      rewrite set_of_variables_in_range_of_subst_unfold, Fset.mem_union, Hz2, Bool.orb_false_l.
      apply Kz.
  + case_eq (Oset.find OX y sigma); [intros y_val y_sigma | intro y_sigma].
    * destruct y_val as [ | g l2]; [trivial | ].
      {
        case_eq (Oset.compare Onat (size (Term f l1)) (size (Term g l2))); intro L.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; rewrite z_sigma.
          rewrite 2 Bool.andb_true_iff; intros [Hz Kz]; split; [ | assumption].
          rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
            Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
          rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
          rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
          rewrite Fset.mem_union, Hz1, Bool.orb_false_r.
          rewrite negb_true_iff, <- not_true_iff_false in Kz.
          rewrite negb_true_iff, <- not_true_iff_false; intro H.
          apply Kz; unfold set_of_variables_in_range_of_subst.
          rewrite Fset.mem_Union; eexists; split; 
          [rewrite in_map_iff; exists (y, Term g l2); split; [apply refl_equal | ] | ].
          + apply (Oset.find_some _ _ _ y_sigma).
          + apply H.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; simpl Oset.find.
          case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
          + rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
            rewrite y_sigma in z_sigma; injection z_sigma; intro; subst z_val; clear z_sigma.
            rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
            rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
              Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
            rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
            rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
            rewrite Fset.mem_union, Hz1, Bool.orb_false_r.
            rewrite negb_true_iff in Kz.
            split; rewrite negb_true_iff, <- not_true_iff_false; intro H.
            * rewrite <- not_true_iff_false in Kz.
              apply Kz; unfold set_of_variables_in_range_of_subst.
              {
                rewrite Fset.mem_Union; eexists; split; 
                [rewrite in_map_iff; exists (y, Term g l2); split; [apply refl_equal | ] | ].
                - apply (Oset.find_some _ _ _ y_sigma).
                - apply H.
              }
            * unfold set_of_variables_in_range_of_subst in H.
              rewrite map_unfold, Fset.Union_unfold, Fset.mem_union in H.
              simpl snd in H; rewrite Hz1, Bool.orb_false_l in H.
              unfold set_of_variables_in_range_of_subst in Kz.
              rewrite H in Kz; discriminate Kz.
          + rewrite z_sigma.
            rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
            rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
              Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
            rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
            rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
            rewrite Fset.mem_union, Hz1, Bool.orb_false_r.
            rewrite negb_true_iff in Kz.
            split; rewrite negb_true_iff, <- not_true_iff_false; intro H.
            * rewrite <- not_true_iff_false in Kz.
              apply Kz; unfold set_of_variables_in_range_of_subst.
              {
                rewrite Fset.mem_Union; eexists; split; 
                [rewrite in_map_iff; exists (y, Term g l2); split; [apply refl_equal | ] | ].
                - apply (Oset.find_some _ _ _ y_sigma).
                - simpl snd; apply H.
              }
            * unfold set_of_variables_in_range_of_subst in H.
              rewrite map_unfold, Fset.Union_unfold, Fset.mem_union in H.
              simpl snd in H; rewrite Hz1, Bool.orb_false_l in H.
              unfold set_of_variables_in_range_of_subst in Kz.
              rewrite H in Kz; discriminate Kz.
        - intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
          intros z_val z_sigma; simpl solved_part; simpl unsolved_part; rewrite z_sigma.
          rewrite 2 Bool.andb_true_iff; intros [Hz Kz]; split; [ | assumption].
          rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
            Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
          rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
          rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Hz', Bool.orb_false_r.
          rewrite Fset.mem_union, Hz1, Bool.orb_false_r.
          rewrite negb_true_iff, <- not_true_iff_false in Kz.
          rewrite negb_true_iff, <- not_true_iff_false; intro H.
          apply Kz; unfold set_of_variables_in_range_of_subst.
          rewrite Fset.mem_Union; eexists; split; 
          [rewrite in_map_iff; exists (y, Term g l2); split; [apply refl_equal | ] | ].
          + apply (Oset.find_some _ _ _ y_sigma).
          + apply H.
      }
    * intro z; case_eq (Oset.find OX z sigma); [ | intros _ Abs; discriminate Abs ].
      intros z_val z_sigma; simpl solved_part; simpl unsolved_part.
      simpl Oset.find; rewrite z_sigma.
      case_eq (Oset.eq_bool OX z y); 
        [ intro z_eq_y; rewrite Oset.eq_bool_true_iff in z_eq_y; subst z; 
          rewrite y_sigma in z_sigma; discriminate z_sigma
        | intro z_diff_y].
      rewrite 2 Bool.andb_true_iff; intros [Hz Kz].
      rewrite negb_true_iff, set_of_variables_in_eq_list_unfold, Fset.mem_union, 
        Bool.orb_false_iff in Hz; destruct Hz as [Hz Hz'].
      rewrite Fset.mem_union, Bool.orb_false_iff in Hz; destruct Hz as [Hz1 Hz2].
      rewrite Hz'; split; [trivial | ].
      rewrite set_of_variables_in_range_of_subst_unfold, Fset.mem_union, Hz1, Bool.orb_false_l.
      apply Kz.
  + case_eq (Oset.eq_bool OF f g); intro Hf; [ | trivial].
    case_eq (Oset.eq_bool Onat (length l1) (length l2)); intro L; [ | trivial].
    intro z; case_eq (Oset.find OX z sigma); 
    [intros z_val z_sigma | intros z_sigma Abs; discriminate Abs].
    simpl solved_part; simpl unsolved_part; rewrite z_sigma.
    rewrite 2 Bool.andb_true_iff; intros [Hz Kz]; split; [ | trivial].
    rewrite negb_true_iff, <- not_true_iff_false; intro H.
    rewrite negb_true_iff, <- not_true_iff_false in Hz; apply Hz.
    unfold set_of_variables_in_eq_list in H; rewrite Fset.mem_Union in H.
    destruct H as [s [Hs H]]; rewrite in_map_iff in Hs.
    destruct Hs as [[t1 t2] [Hs K]]; subst s.
    rewrite combine_unfold in K; destruct (in_app_or _ _ _ K) as [K1 | K1]; clear K.
    * simpl fst in H; simpl snd in H.
      rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Bool.orb_true_iff.
      left; rewrite 2 (variables_t_unfold _ (Term _ _)).
      rewrite Oset.eq_bool_true_iff in L.
      clear Hst Hz; revert l2 L K1.
      induction l1 as [ | u1 l1]; intros [ | u2 l2] L K1; try (discriminate L || contradiction K1).
      simpl in L; injection L; clear L; intro L.
      simpl in K1; rewrite combine_unfold in K1.
      rewrite 2 (map_unfold _ (_ :: _)), 2 (Fset.Union_unfold _ (_ :: _)), 3 Fset.mem_union.
      {
        destruct (in_app_or _ _ _ K1) as [K2 | K2].
        - assert (IH := IHl1 _ L K2).
          rewrite Fset.mem_union, Bool.orb_true_iff in IH; destruct IH as [IH | IH];
          rewrite IH; repeat rewrite Bool.orb_true_r; trivial.
        - simpl in K2; destruct K2 as [K2 | K2]; [ | contradiction K2].
          injection K2; clear K2; do 2 intro; subst t1 t2.
          rewrite Fset.mem_union, Bool.orb_true_iff in H; destruct H as [H | H];
          rewrite H; repeat rewrite Bool.orb_true_r; trivial.
      } 
    * rewrite set_of_variables_in_eq_list_unfold, Fset.mem_union, Bool.orb_true_iff; right.
      unfold set_of_variables_in_eq_list; rewrite Fset.mem_Union.
      eexists; split; 
      [rewrite in_map_iff; exists (t1, t2); split; [apply refl_equal | ] | ]; trivial.
Qed.

Lemma Inv_solved_part_inv :
  forall pb,
  match decomposition_step pb with
   | Normal pb' => Inv_solved_part pb -> Inv_solved_part pb'
   | _ => True
   end.
Proof.
intro pb; assert (H := is_a_solved_var_inv pb).
case_eq (decomposition_step pb); trivial.
intros pb' H'; rewrite H' in H.
unfold Inv_solved_part.
intros Inv_pb z.
case_eq (Oset.find OX z (solved_part pb')); [ | intros; trivial].
intros [v | ] Hv; [ | trivial].
unfold decomposition_step in H'; destruct pb as [sigma l]; 
assert (Hz := Inv_pb z).
simpl solved_part in *; simpl unsolved_part in *.
destruct l as [ | [s t] l]; [discriminate H' | ].
case_eq (Oset.eq_bool (OT OX OF) s t); intro Hst; rewrite Hst in H'.
- injection H'; clear H'; intro; subst pb'.
  simpl in Hv; rewrite Hv in Hz.
  apply H; assumption.
- destruct s as [x | f l1]; destruct t as [y | g l2].
  + assert (x_diff_y : x <> y).
    {
      intro; subst y; rewrite Oset.eq_bool_refl in Hst; discriminate Hst.
    }         
    case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intros x_sigma].
    * rewrite (Oset.find_some_map _ _ _ _ x_sigma) in H'; injection H'; clear H'; intro; subst pb'.
      simpl in Hv.
      {
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        - rewrite z_eq_x in Hv; rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          injection Hv; clear Hv; intro; subst v.
          unfold is_a_solved_var; simpl; 
          rewrite Oset.eq_bool_refl, set_of_variables_in_eq_list_unfold, 2 Fset.mem_union.
          rewrite (var_not_in_apply_renaming_list _ x_diff_y), Bool.orb_false_r.
          rewrite set_of_variables_in_range_of_subst_unfold, Fset.mem_union.
          rewrite (var_not_in_apply_renaming_range_of_subst _ x_diff_y), Bool.orb_false_r.
          replace (x inS? variables_t FX (Var y)) with false.
          + rewrite Bool.andb_true_r, Bool.orb_false_l.
            rewrite (var_not_in_apply_renaming_term _ _ x_diff_y); trivial.
          + apply sym_eq; 
            rewrite <- not_true_iff_false, in_variables_t_var; intro; apply x_diff_y; subst; 
            trivial.
        - rewrite z_diff_x in Hv.
          case_eq (Oset.find OX z sigma); [intros z_val z_sigma | intro z_sigma].
          + rewrite (Oset.find_some_map _ _ _ _ z_sigma) in Hv.
            destruct z_val as [z' | ]; [ | discriminate Hv].
            rewrite z_sigma in Hz.
            apply H; assumption.
          + rewrite (Oset.find_none_map _ _ _ _ z_sigma) in Hv; discriminate Hv.
      }
    * rewrite (Oset.find_none_map _ _ _ _ x_sigma) in H'; injection H'; clear H'; intro; subst pb'.
      simpl in Hv.
      {
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        - rewrite z_eq_x in Hv; rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          injection Hv; clear Hv; intro; subst v.
          unfold is_a_solved_var; simpl; rewrite Oset.eq_bool_refl.
          rewrite (var_not_in_apply_renaming_list _ x_diff_y).
          rewrite set_of_variables_in_range_of_subst_unfold, Fset.mem_union.
          rewrite (var_not_in_apply_renaming_range_of_subst _ x_diff_y), Bool.orb_false_r.
          replace (x inS? variables_t FX (Var y)) with false; trivial.
          apply sym_eq; 
            rewrite <- not_true_iff_false, in_variables_t_var; intro; apply x_diff_y; subst; 
            trivial.
        - rewrite z_diff_x in Hv.
          case_eq (Oset.find OX z sigma); [intros z_val z_sigma | intro z_sigma].
          + rewrite (Oset.find_some_map _ _ _ _ z_sigma) in Hv.
            destruct z_val as [z' | ]; [ | discriminate Hv].
            rewrite z_sigma in Hz.
            apply H; assumption.
          + rewrite (Oset.find_none_map _ _ _ _ z_sigma) in Hv; discriminate Hv.
      }
  + case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intros x_sigma].
    * rewrite x_sigma in H'; destruct x_val as [ | f l1]; [discriminate H' | ].
      {
        case_eq (Oset.compare Onat (size (Term g l2)) (size (Term f l1))); 
        intro L; rewrite L in H'; injection H'; clear H'; intro; subst pb'; 
        simpl solved_part in *.
        - rewrite Hv in Hz; apply H; assumption.
        - simpl in Hv.
          case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
          + rewrite z_eq_x in Hv; rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
            discriminate Hv.
          + rewrite z_diff_x in Hv.
            rewrite Hv in Hz.
            apply H; assumption.
        - rewrite Hv in Hz; apply H; assumption.
      }
    * rewrite x_sigma in H'; injection H'; clear H'; intro; subst pb'; simpl solved_part in *.
      simpl in Hv.
      {
        case_eq (Oset.eq_bool OX z x); [intro z_eq_x | intro z_diff_x].
        - rewrite z_eq_x in Hv; rewrite Oset.eq_bool_true_iff in z_eq_x; subst z.
          discriminate Hv.
        - rewrite z_diff_x in Hv.
          apply H; rewrite Hv in Hz; assumption.
      }
  + case_eq (Oset.find OX y sigma); [intros y_val y_sigma | intros y_sigma].
    * rewrite y_sigma in H'; destruct y_val as [ | g l2]; [discriminate H' | ].
      {
        case_eq (Oset.compare Onat (size (Term f l1)) (size (Term g l2))); 
        intro L; rewrite L in H'; injection H'; clear H'; intro; subst pb'; 
        simpl solved_part in *.
        - rewrite Hv in Hz; apply H; assumption.
        - simpl in Hv.
          case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
          + rewrite z_eq_y in Hv; rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
            discriminate Hv.
          + rewrite z_diff_y in Hv.
            rewrite Hv in Hz.
            apply H; assumption.
        - rewrite Hv in Hz; apply H; assumption.
      }
    * rewrite y_sigma in H'; injection H'; clear H'; intro; subst pb'; simpl solved_part in *.
      simpl in Hv.
      {
        case_eq (Oset.eq_bool OX z y); [intro z_eq_y | intro z_diff_y].
        - rewrite z_eq_y in Hv; rewrite Oset.eq_bool_true_iff in z_eq_y; subst z.
          discriminate Hv.
        - rewrite z_diff_y in Hv.
          apply H; rewrite Hv in Hz; assumption.
      }
  + case_eq (Oset.eq_bool OF f g); intro Hf; rewrite Hf in H'; [ | discriminate H'].
    rewrite Oset.eq_bool_true_iff in Hf; subst g.
    case_eq (Oset.eq_bool Onat (length l1) (length l2)); 
      intro L; rewrite L in H'; [ | discriminate H'].
    injection H'; clear H'; intro; subst pb'; simpl solved_part in *.
    rewrite Hv in Hz; apply H; assumption.
Qed.

Lemma decompose_is_sound : 
  forall n (l : list (term * term)) (sigma theta : substitution dom symbol),
  match decompose n (mk_pb sigma l) with
  | Some pb' =>
      is_a_solution pb' theta -> is_a_solution (mk_pb sigma l) theta
  | None => is_a_solution (mk_pb sigma l) theta -> False
  end.
Proof.
intro n; induction n as [ | n]; intros l sigma theta; simpl.
exact (fun H => H).
generalize (decomposition_step_is_sound l sigma theta).
generalize (@decomposition_step_is_complete l sigma theta).
destruct (decomposition_step (mk_pb sigma l)) as [ [sigma' l'] | [sigma' l'] | ].
intros Hc Hs; generalize (IHn l' sigma' theta).
destruct (decompose n (mk_pb sigma' l')) as [pb'' | ].
intros H' H''; apply Hs; apply H'; assumption.
intros H' H''; apply H'; apply Hc; assumption.
intros _; exact (fun H => H).
intros _; exact (fun H => H).
Qed.

Lemma decompose_is_complete:
  forall n (l : list (term * term)) (sigma theta : substitution dom symbol),
  is_a_solution (mk_pb sigma l) theta ->
  match decompose n (mk_pb sigma l) with
  | Some pb' => is_a_solution pb' theta
  | None => False
  end.
Proof.
intro n; induction n as [ | n]; intros l sigma theta; simpl.
exact (fun H => H).
generalize (decomposition_step_is_sound l sigma theta).
generalize (@decomposition_step_is_complete l sigma theta).
destruct (decomposition_step (mk_pb sigma l)) as [ [sigma' l'] | [sigma' l'] | ].
intros Hc Hs; generalize (IHn l' sigma' theta).
destruct (decompose n (mk_pb sigma' l')) as [pb'' | ].
intros H' H''; apply H'; apply Hc; assumption.
intros H' H''; apply H'; apply Hc; assumption.
exact (fun H _ => H).
intros _; exact (fun H => H).
Qed.

Lemma size_renaming :
  forall x y t, size (apply_subst OX ((x, Var (symbol := symbol) y) :: nil) t) = size t.
Proof.
intros x y t; pattern t; apply term_rec3; clear t.
- intro v; simpl.
  case (Oset.eq_bool OX v x); simpl; trivial.
- intros f l IH; simpl.
  apply f_equal; induction l as [ | t1 l]; simpl; [trivial | ].
  apply f_equal2; [apply IH; left; trivial | ].
  apply IHl; intros; apply IH; right; assumption.
Qed.

Lemma list_size_size_renaming :
  forall x y l, 
    list_size (size (symbol:=symbol)) (map (apply_subst OX ((x, Var y) :: nil)) l) =
   list_size (size (symbol:=symbol)) l.
Proof.
intros x y l; induction l as [ | t1 l]; simpl; [trivial | ].
  apply f_equal2; [apply size_renaming | apply IHl].
Qed.

Lemma size_minus_power4_renaming :
  forall x y s1 t1,
    size_minus power4 (apply_subst OX ((x, Var y) :: nil) s1)
               (apply_subst OX ((x, Var y) :: nil) t1) = 
    size_minus power4 s1 t1.
Proof.
intros x y s1; pattern s1; apply term_rec3; clear s1.
- intros x1 [x2 | f2 l2]; simpl.
  + case (Oset.eq_bool OX x1 x); case (Oset.eq_bool OX x2 x); trivial.
  + case (Oset.eq_bool OX x1 x); trivial.
- intros f1 l1 Hl1 [x2 | f2 l2].
  + simpl; case (Oset.eq_bool OX x2 x); rewrite list_size_size_renaming; trivial.
  + simpl apply_subst; rewrite 2 size_minus_unfold.
    revert l2; induction l1 as [ | t1 l1]; [intro l2; trivial | ].
    intros [ | t2 l2]; simpl; apply f_equal2.
    * apply f_equal; apply size_renaming.
    * apply (IHl1 (fun x h => Hl1 x (or_intror _ h)) nil).
    * apply Hl1; left; apply refl_equal.
    * apply (IHl1 (fun x h => Hl1 x (or_intror _ h)) l2).
Qed.

Lemma size_common_renaming :
  forall x y s1 t1,
    size_common (apply_subst OX ((x, Var y) :: nil) s1)
               (apply_subst OX ((x, Var y) :: nil) t1) = 
    size_common s1 t1.
Proof.
intros x y s1; pattern s1; apply term_rec3; clear s1.
- intros x1 [x2 | f2 l2]; simpl.
  + case (Oset.eq_bool OX x1 x); case (Oset.eq_bool OX x2 x); trivial.
  + case (Oset.eq_bool OX x1 x); trivial.
- intros f1 l1 Hl1 [x2 | f2 l2].
  + simpl; case (Oset.eq_bool OX x2 x); trivial.
  + simpl apply_subst; rewrite 2 size_common_unfold; apply f_equal.
    revert l2; induction l1 as [ | t1 l1]; [intro l2; trivial | ].
    intros [ | t2 l2]; simpl; [trivial | ].
    apply f_equal2.
    * apply Hl1; left; apply refl_equal.
    * apply (IHl1 (fun x h => Hl1 x (or_intror _ h)) l2).
Qed.

Lemma list_size_eqt_meas2_power4_renaming :
  forall x y l, 
    list_size
      (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
      (map (fun uv : term * term => 
              match uv with
                  | (u, v) => (apply_subst OX ((x, Var y) :: nil) u, 
                               apply_subst OX ((x, Var y) :: nil) v)
              end) l) =
    list_size (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t) l.
Proof.
intros x y l; induction l as [ | [s1 t1] l]; [apply refl_equal | ].
rewrite map_unfold, 2 (list_size_unfold _ (_ :: _)); apply f_equal2; [ | apply IHl].
clear l IHl.
unfold eqt_meas2; apply f_equal2; [apply f_equal2; apply size_minus_power4_renaming | ].
apply size_common_renaming.
Qed.

Lemma list_size_eqt_meas2_power4_subst_renaming :
  forall x y l k,
    list_size
     (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
     (map
        (fun x0 : variable dom =>
         (Var x0,
         apply_subst OX
           (map
              (fun zt : variable dom * term =>
               let (z, t) := zt in
               (z, apply_subst OX ((x, Var y) :: nil) t)) l)
           (Var x0))) k) =
   list_size
     (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
     (map
        (fun x0 : variable dom =>
         (Var x0, apply_subst OX l (Var x0))) k).
Proof.
intros x y l k.
induction k as [ | v1 k]; [apply refl_equal | ].
simpl; apply f_equal2.
- unfold eqt_meas2; apply f_equal2; [apply f_equal2 | ].
  + case_eq (Oset.find OX v1 l).
    * intros t1 Hv1; rewrite (Oset.find_some_map _ _ _ _ Hv1).
      destruct t1 as [x1 | f1 l1]; simpl; [case (Oset.eq_bool OX x1 x) | ]; trivial.
    * intro Hv1; rewrite (Oset.find_none_map _ _ _ _ Hv1); trivial.
  + case_eq (Oset.find OX v1 l).
    * intros t1 Hv1; rewrite (Oset.find_some_map _ _ _ _ Hv1).
      destruct t1 as [x1 | f1 l1]; simpl; [case (Oset.eq_bool OX x1 x) | ]; trivial.
      rewrite list_size_size_renaming; apply refl_equal.
    * intro Hv1; rewrite (Oset.find_none_map _ _ _ _ Hv1); trivial.
  + case_eq (Oset.find OX v1 l).
    * intros t1 Hv1; rewrite (Oset.find_some_map _ _ _ _ Hv1).
      destruct t1 as [x1 | f1 l1]; simpl; [case (Oset.eq_bool OX x1 x) | ]; trivial.
    * intro Hv1; rewrite (Oset.find_none_map _ _ _ _ Hv1); trivial.
- apply IHk.
Qed.

Lemma list_size_eqt_meas2_power4_subst_dec :
forall x sigma l,      
list_size (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
      (map
         (fun x0 : variable dom =>
            (Var x0, apply_subst OX ((x, Var x) :: sigma) (Var x0))) l) <=
list_size (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
          (map
             (fun x0 : variable dom =>
                (Var x0, apply_subst OX sigma (Var x0))) l).
Proof.
intros x sigma l; induction l as [ | x1 l]; [apply le_n | ].
simpl; apply plus_le_compat; [ | apply IHl].
unfold eqt_meas2; case (Oset.eq_bool OX x1 x); simpl.
- case (Oset.find OX x1 sigma). 
  + intros [x2 | f2 l2]; [apply le_n | ].
    apply le_n_S; apply le_0_n.
  + simpl; apply le_n.
- case (Oset.find OX x1 sigma); intros; apply le_n.
Qed.
    
Lemma power4_ge_one : forall n, 1 <= power4 n.
Proof.
fix power4_ge_one 1.
intro n; case n; clear n.
apply le_n.
intro n; simpl.
apply le_trans with (power4 n).
apply power4_ge_one.
apply le_plus_l.
Qed.

Lemma power4_unfold : forall n, power4 (S n) = 4 * power4 n.
Proof.
intro n; apply refl_equal.
Qed.

Lemma power4_mon : forall n m, n <= m -> power4 n <= power4 m.
Proof.
fix power4_mon 1.
intro n; case n; clear n.
intros m _; simpl; apply power4_ge_one.
intros n m; case m; clear m.
intro H; inversion H.
intros m H; do 2 rewrite power4_unfold.
apply mult_le_compat_l; apply power4_mon; apply le_S_n; assumption.
Qed.

Lemma eqt_meas2_strict_mon :
  forall x f l1 g l2,
    size (Term g l2) < size (Term f l1) ->
    eqt_meas2 power4 (Var x) (Term g l2) < eqt_meas2 power4 (Var x) (Term f l1).
Proof.
intros x f l1 g l2 L; simpl in L; generalize (le_S_n _ _ L); clear L; intro L.
unfold eqt_meas2; simpl size_common; rewrite <- 2 plus_n_O.
simpl size_minus at 1 3; apply plus_lt_compat_l.
simpl; apply plus_lt_le_compat.
- refine (lt_le_trans _ _ _ _ (power4_mon L)).
  rewrite power4_unfold.
  set (n := list_size (size (symbol:=symbol)) l2).
  generalize (power4_ge_one n).
  set (m := power4 n); clearbody n m; intro Hm.
  apply lt_le_trans with (1 + m); [apply le_n | ].
  simpl mult; apply plus_le_compat; [assumption | ].
  apply le_plus_l.
- rewrite <- 2 plus_n_O.
  do 2 (apply plus_le_compat; [apply power4_mon; apply lt_le_weak; assumption | ]).
  apply power4_mon; apply lt_le_weak; assumption.
Qed.

Lemma size_minus_le : 
       forall f, (forall n m, 1 <= n -> 1 <= m -> (f n) + (f m) <= f (n + m)) -> 
                      forall t1 t2, size_minus f t1 t2 <= f (size t1).
Proof.
intros f Convf t1; pattern t1; apply term_rec3; clear t1.
intros x1 [x2 | f2 l2]; simpl; [apply le_O_n | apply le_n].
intros f1 l1 IH [x2 | f2 l2].
apply le_n.
rewrite size_minus_unfold; simpl.
revert l2; induction l1 as [ | t1 l1]; intros [ | t2 l2]; simpl.
apply le_O_n.
apply le_O_n.
apply le_trans with (f (size t1) + f (1 + list_size (@size _ _) l1)).
apply plus_le_compat_l; apply IHl1; intros; apply IH; right; assumption.
replace (S (size t1 + list_size (@size _ _) l1)) with 
  (size t1 + (1 + list_size (@size _ _) l1)).
apply Convf.
apply size_ge_one.
apply le_plus_l.
rewrite plus_comm; simpl; rewrite plus_comm; apply refl_equal.
apply le_trans with (f (size t1) + f (1 + list_size (@size _ _) l1)).
apply plus_le_compat.
apply IH; left; apply refl_equal.
 apply IHl1; intros; apply IH; right; assumption.
replace (S (size t1 + list_size (@size _ _) l1)) with 
  (size t1 + (1 + list_size (@size _ _) l1)).
apply Convf.
apply size_ge_one.
apply le_plus_l.
rewrite plus_comm; simpl; rewrite plus_comm; apply refl_equal.
Qed.

Lemma size_minus_list_le : 
  forall f, (forall n m, 1 <= n -> 1 <= m -> (f n) + (f m) <= f (n + m)) -> 
    (forall n, 1 <= n -> 1 <= f n) -> 
    forall l1 l2, size_minus_list f l1 l2 <= f (list_size (@size _ _) l1).
Proof.
intros f Convf Hf l1.
induction l1 as [ | t1 l1]; simpl.
intros _; apply le_O_n.

destruct l1 as [ | s1 l1].
destruct l2 as [ | t2 l1].
simpl; do 2 rewrite <- plus_n_O; apply le_n.
simpl; do 2 rewrite <- plus_n_O; apply size_minus_le; assumption.
intro l2; apply le_trans with (f (size t1) + f (list_size (@size _ _) (s1 :: l1))).
destruct l2 as [ | t2 l2].
apply plus_le_compat_l; apply IHl1; intros; apply IH; right; assumption.
apply plus_le_compat.
apply size_minus_le; assumption.
apply IHl1.
apply Convf.
apply size_ge_one.
apply le_trans with (size s1); [ apply size_ge_one | apply le_plus_l].
Qed.

Lemma power4_convex : forall n m, 1 <= n -> 1 <= m -> power4 n + power4 m <= power4 (n + m).
Proof.
intro n; case n; clear n.
intros m H; inversion H.
intros n m; case m; clear m.
intros H H'; inversion H'.
intros m _ _; do 2 rewrite power4_unfold.
rewrite <- mult_plus_distr_l.
simpl plus; rewrite power4_unfold.
apply mult_le_compat_l.
rewrite (plus_comm n); simpl plus; rewrite (plus_comm m).
rewrite power4_unfold.
apply le_trans with (power4 (n + m) + power4 (n + m)).
apply plus_le_compat.
apply power4_mon; apply le_plus_l.
apply power4_mon; apply le_plus_r.
simpl; apply plus_le_compat_l; apply le_plus_l.
Qed.

Lemma power4_strict_mon : forall n m, 1 <= n -> n < m -> power4 n < power4 m.
Proof.
intros n m Hn Hm.
apply lt_le_trans with (power4 (S n)).
rewrite power4_unfold.
pattern (power4 n) at 1.
replace (power4 n) with (1 * power4 n); [ | simpl; rewrite <- plus_n_O; apply refl_equal].
apply mult_lt_compat_r.
do 2 apply le_S; apply le_n.
apply power4_ge_one.
apply power4_mon; assumption.
Qed.

Lemma size_common_le : forall s t, size_common s t <= size s.
Proof.
intro s; pattern s; apply term_rec3; clear s.
intros x [y | g k]; simpl.
apply le_n.
apply le_O_n.
intros f l IH [y | g k].
simpl; apply le_O_n.
rewrite size_common_unfold; simpl.
apply le_n_S.
revert k; induction l as [ | t l]; intros [ | s k]; simpl.
apply le_O_n.
apply le_O_n.
apply le_O_n.
apply plus_le_compat.
apply IH; left; apply refl_equal.
apply IHl; intros; apply IH; right; assumption.
Qed.

Lemma size_common_comm : forall s t, size_common s t = size_common t s.
Proof.
intro s; pattern s; apply term_rec3; clear s.
intros x [y | g k]; apply refl_equal.
intros f l IH [y | g k].
apply refl_equal.
do 2 rewrite size_common_unfold; apply f_equal.
clear - IH; revert k; induction l as [ | s l]; intros [ | t k].
apply refl_equal.
apply refl_equal.
apply refl_equal.
simpl; rewrite IH; [rewrite IHl; [ apply refl_equal | intros; apply IH; right; assumption] | left; apply refl_equal].
Qed.

Lemma merge_decr_aux2 :
   forall x f1 l1 f2 l2 , 
     size (Term f2 l2) <= size (Term f1 l1) ->
     eqt_meas2 power4 (Term f1 l1) (Term f2 l2) < eqt_meas2 power4 (Var x) (Term f1 l1).
Proof. 
intros x f1 l1 f2 l2 H; unfold eqt_meas2.
simpl in H; generalize (le_S_n _ _ H); clear H; intro H.
do 2 rewrite size_minus_unfold.
destruct l1 as [ | t1 l1]; destruct l2 as [ | t2 l2].
(* 1/4 l1 = nil, l2 = nil *)
simpl; do 2 apply le_n_S; apply le_O_n.
(* 1/3 l1 = nil, l2 = _ :: _ *)
absurd (1 <= 0).
intro H'; inversion H'.
apply le_trans with (size t2).
apply size_ge_one.
apply le_trans with (list_size (@size _ _) (t2 :: l2)).
apply le_plus_l.
assumption.
(* 1/2 l1 = _ :: _, l2 = nil *)
replace (size_minus_list power4 nil (t1 :: l1)) with 0; [ rewrite <- plus_n_O | apply refl_equal].
simpl size_common; rewrite <- plus_n_O.
set (n := size_minus power4 (Var x) (Term f1 (t1 :: l1))) in *; simpl in n.
rewrite plus_comm; 
pattern (size_minus power4 (Term f1 (t1 :: l1)) (Var x)); 
pattern (size_minus_list power4 (t1 :: l1) nil);
simpl plus; cbv beta; do 2 apply le_n_S.
do 2 apply le_S.
apply le_trans with (power4 (list_size (@size _ _) (t1 :: l1))).
apply size_minus_list_le.
apply power4_convex.
intros; apply power4_ge_one.
apply le_trans with (power4 (S (list_size (@size _ _) (t1 :: l1)))).
apply lt_le_weak; apply power4_strict_mon.
apply le_trans with (size t1).
apply size_ge_one.
apply le_plus_l.
apply le_n.
simpl; apply le_n.
(* 1/1 l1 = _ :: _, l2 = _ :: _ *)
apply le_lt_trans with (size_minus_list power4 (t1 :: l1) (t2 :: l2) + size_minus_list power4 (t2 :: l2) (t1 :: l1) + size (Term f1 (t1 :: l1))).
apply plus_le_compat_l; apply size_common_le.
set (n := size_minus power4 (Var x) (Term f1 (t1 :: l1))) in *; simpl in n.
set (m := size_common (Var x) (Term f1 (t1 :: l1))) in *; simpl in m.
rewrite <- plus_n_O.
rewrite plus_comm.
replace (size_minus power4 (Term f1 (t1 :: l1)) (Var x)) with (power4 (size (Term f1 (t1 :: l1)))); [ | apply refl_equal].
replace (size (Term f1 (t1 :: l1))) with (1 + list_size (@size _ _) (t1 :: l1)); [ | apply refl_equal].
set (k1 := t1 :: l1) in *; set (k2 := t2 :: l2) in *.
apply le_lt_trans with (1 + list_size (@size _ _) k1 + (power4 (list_size (@size _ _) k1)) + (power4 (list_size (@size _ _) k1))).
do 3 rewrite <- plus_assoc; do 2 apply plus_le_compat_l.
apply plus_le_compat.
apply size_minus_list_le.
apply power4_convex.
intros; apply power4_ge_one.
apply le_trans with (power4 (list_size (@size _ _) k2)).
apply size_minus_list_le.
apply power4_convex.
intros; apply power4_ge_one.
apply power4_mon; assumption.
set (p := (list_size (@size _ _) k1)) in *; simpl.
do 2 apply le_n_S; do 2 apply le_S.
rewrite <- plus_assoc.
apply plus_le_compat.
clear; clearbody p; induction p as [ | p]; simpl.
apply le_O_n.
replace (S p) with (1 + p); [ | apply refl_equal].
apply plus_le_compat.
apply power4_ge_one.
apply le_trans with (power4 p).
assumption.
apply le_plus_l.
apply plus_le_compat_l.
apply le_plus_l.
Qed.

Lemma le_plus_trans_alt : forall n m p : nat, n <= m -> n <= p + m.
Proof.
do 3 intro; rewrite plus_comm; apply le_plus_trans.
Qed.

Lemma remove_trivial_eq_decreases :
  forall s1 s2 l sigma, Oset.eq_bool (OT OX OF) s1 s2 = true ->
                        measure (mk_pb sigma l) < measure (mk_pb sigma ((s1, s2) :: l)).
Proof.
intros s1 s2 l sigma Hs.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((s1, s2) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((s1, s2) :: l))).
unfold decomposition_step in *; simpl in H1, H2; rewrite Hs in H1, H2.
rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le1_lt.
- unfold phi1; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intros x Hx.
  rewrite Fset.mem_filter, Bool.andb_true_iff in Hx.
  rewrite Fset.mem_filter, Bool.andb_true_iff; split.
  + apply H1; apply (proj1 Hx).
  + rewrite negb_true_iff, <- not_true_iff_false.
    intro Kx.
    rewrite (H2 _ Kx) in Hx.
    destruct Hx as [_ Hx]; discriminate Hx.
- unfold psi2; simpl solved_part; apply plus_lt_compat_r.
  simpl unsolved_part; rewrite (list_size_unfold _ (_ :: _)).
  apply lt_le_trans with 
      (1 + list_size (fun st : term * term => let (s0, t) := st in eqt_meas2 power4 s0 t) l).
  + apply le_n.
  + apply plus_le_compat_r.
    unfold eqt_meas2.
    destruct s1 as [x1 | g1 k1]; destruct s2 as [x2 | g2 k2]; simpl.
    * apply le_n.
    * apply le_n_S; apply le_O_n.
    * apply le_plus_trans.
      rewrite plus_comm; simpl; apply le_n_S; apply le_O_n.
    * rewrite plus_comm; simpl.
      apply le_n_S; apply le_O_n.
- unfold psi3; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intro x.
  rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff; simpl solved_part; simpl unsolved_part.
  intros [H3 H4]; split; [ | assumption].
  apply H1; assumption.
Qed.

Lemma coalesce1_decreases :
 forall x y l sigma x_val, 
   x <> y -> Oset.find OX x sigma = Some x_val ->
   let x_to_y t := apply_subst OX ((x, Var y) :: nil) t in
   measure (mk_pb ((x, Var y) 
                     :: map (fun zt => match zt with (z, t) => (z, x_to_y t) end) sigma)
                  ((Var y, x_to_y x_val) 
                     :: map (fun uv => match uv with (u,v) => (x_to_y u, x_to_y v) end) l)) <
   measure (mk_pb sigma ((Var x, Var y) :: l)).
Proof.
intros x y l sigma x_val x_diff_y x_sigma x_to_y.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((Var x, Var y) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((Var x, Var y) :: l))).
unfold decomposition_step in *; simpl in H1, H2.
assert (x_diff_y' : Oset.eq_bool (OT OX OF) (Var x) (Var y) = false).
{
  rewrite <- not_true_iff_false, Oset.eq_bool_true_iff.
  intro H; injection H; clear H; intro H; apply x_diff_y; assumption.
}
rewrite x_diff_y', (Oset.find_some_map _ _ _ _ x_sigma) in H1, H2.
rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le0_lt.
- unfold phi1; apply Fset.cardinal_strict_subset with x.
  + rewrite Fset.subset_spec; intros z Hz.
    rewrite Fset.mem_filter, Bool.andb_true_iff in Hz.
    rewrite Fset.mem_filter, Bool.andb_true_iff; split.
    * apply H1; apply (proj1 Hz).
    * rewrite negb_true_iff, <- not_true_iff_false; intro H3.
      rewrite negb_true_iff, <- not_true_iff_false in Hz; 
        apply (proj2 Hz); apply H2; apply H3.
  + rewrite Fset.mem_filter, Bool.andb_false_iff; right.
    unfold vars_of_pb, is_a_solved_var; simpl.
    rewrite Oset.eq_bool_refl.
    rewrite negb_false_iff, Bool.andb_true_iff, 2 negb_true_iff.
    rewrite set_of_variables_in_eq_list_unfold, set_of_variables_in_range_of_subst_unfold.
    rewrite 3 Fset.mem_union, (variables_t_unfold _ (Var y)), 3 Bool.orb_false_iff.
    rewrite Fset.singleton_spec, <- not_true_iff_false, Oset.eq_bool_true_iff;
      repeat split; trivial.
    * apply var_not_in_apply_renaming_term; trivial.
    * unfold x_to_y; rewrite var_not_in_apply_renaming_list; trivial.
    * rewrite <- not_true_iff_false; intro Hx.
      unfold set_of_variables_in_range_of_subst in Hx.
      rewrite map_map, Fset.mem_Union in Hx.
      destruct Hx as [s [Hs Hx]]; rewrite in_map_iff in Hs.
      destruct Hs as [[x1 t2] [Hs Ht]]; subst s; simpl in Hx.
      unfold x_to_y in Hx; 
        rewrite (var_not_in_apply_renaming_term _ _ x_diff_y) in Hx; discriminate Hx.
  + rewrite Fset.mem_filter.
    unfold vars_of_pb, is_a_solved_var; simpl solved_part; simpl unsolved_part.
    rewrite set_of_variables_in_eq_list_unfold, 3 Fset.mem_union, (variables_t_unfold _ (Var x)).
    rewrite Fset.singleton_spec, Oset.eq_bool_refl, Bool.andb_true_l.
    rewrite x_sigma; apply refl_equal.
- unfold psi2, x_to_y; simpl solved_part; simpl unsolved_part.
  set (sigma' := (x, Var x) :: sigma).
  assert (Hsig := refl_equal sigma'); unfold sigma' at 2 in Hsig; clearbody sigma'.
  replace ((x, Var y)
             :: map
             (fun zt : variable dom * term =>
                let (z, t) := zt in
                (z, apply_subst OX ((x, Var y) :: nil) t)) sigma) with
  (map (fun zt : variable dom * term =>
          let (z, t) := zt in
          (z, apply_subst OX ((x, Var y) :: nil) t)) sigma');
  [ | rewrite Hsig; simpl; rewrite Oset.eq_bool_refl; apply refl_equal].
  rewrite 2 (list_size_unfold _ (_ :: _)), list_size_eqt_meas2_power4_renaming.
  unfold substitution_to_eq_list; rewrite list_size_eqt_meas2_power4_subst_renaming.
  rewrite (Fset.elements_spec1 _ _ _ (domain_of_subst_inv _ _ _)), Hsig, domain_of_subst_unfold.
  assert (Hx : In x ({{{domain_of_subst FX sigma}}})).
  {
    apply Fset.mem_in_elements; unfold domain_of_subst.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    exists (x, x_val); split; trivial.
    apply (Oset.find_some _ _ _ x_sigma).
  }
  assert (Hd : x addS domain_of_subst FX sigma =S= domain_of_subst FX sigma).
  {
    rewrite Fset.equal_spec; intro z; rewrite Fset.add_spec.
    case_eq (Oset.eq_bool OX z x); intro Hz; [ | apply refl_equal].
    rewrite Oset.eq_bool_true_iff in Hz; subst z.
    simpl; apply sym_eq; apply Fset.in_elements_mem; apply Hx.
  }
  rewrite (Fset.elements_spec1 _ _ _ Hd).
  destruct (in_split _ _ Hx) as [l1 [l2 Kx]]; rewrite Kx; clear Hx.
  rewrite 2 map_app, 2 (map_unfold _ (_ :: _)), 2 list_size_app, 2 (list_size_unfold _ (_ :: _)).
  repeat rewrite plus_assoc; apply plus_le_compat; [ | apply list_size_eqt_meas2_power4_subst_dec].
  rewrite plus_comm; repeat rewrite <- plus_assoc; apply plus_le_compat;
  [simpl; rewrite Oset.eq_bool_refl; unfold eqt_meas2; simpl; apply le_n | ].
  rewrite plus_comm; repeat rewrite <- plus_assoc; apply plus_le_compat_l.
  apply plus_le_compat; [apply list_size_eqt_meas2_power4_subst_dec | ].
  simpl; rewrite x_sigma; unfold eqt_meas2; destruct x_val; simpl;
  [ | rewrite list_size_size_renaming; apply le_n].
  case (Oset.eq_bool OX v x); apply le_n.
- (* 1/1 *)
  unfold psi3; apply Fset.cardinal_subset; rewrite Fset.subset_spec; intro z.
  rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  intros [Hz Kz]; split.
  + apply H1; apply Hz.
  + rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff in Kz.
    rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff; intro Jz; apply Kz.
    simpl; right; rewrite map_map.
    rewrite in_map_iff in Jz; destruct Jz as [[_z t] [_Jz Jz]]; simpl in _Jz; subst _z.
    rewrite in_map_iff; eexists; split; [ | apply Jz]; trivial.
Qed.

Lemma coalesce2_decreases :
  forall x y l sigma, 
    x <> y -> 
    Oset.find OX x sigma = None ->
    measure (mk_pb ((x, Var y)
                    :: map
                         (fun vv_sigma : variable dom * term =>
                          let (v, v_sigma) := vv_sigma in
                          (v,
                          apply_subst OX ((x, Var y) :: nil) v_sigma))
                         sigma)
                  (map
                        (fun uv : term * term =>
                         let (u, v) := uv in
                         (apply_subst OX ((x, Var y) :: nil) u,
                         apply_subst OX ((x, Var y) :: nil) v)) l)) <
   measure (mk_pb sigma ((Var x, Var y) :: l)).
Proof.
intros x y l sigma x_diff_y x_sigma.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((Var x, Var y) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((Var x, Var y) :: l))).
unfold decomposition_step in *; simpl in H1, H2.
assert (x_diff_y' : Oset.eq_bool (OT OX OF) (Var x) (Var y) = false).
{
  rewrite <- not_true_iff_false, Oset.eq_bool_true_iff.
  intro H; injection H; clear H; intro H; apply x_diff_y; assumption.
}
rewrite x_diff_y', (Oset.find_none_map _ _ _ _ x_sigma) in H1, H2.
rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le0_lt.
- unfold phi1; apply Fset.cardinal_strict_subset with x.
  + rewrite Fset.subset_spec; intros z Hz.
    rewrite Fset.mem_filter, Bool.andb_true_iff in Hz.
    rewrite Fset.mem_filter, Bool.andb_true_iff; split.
    * apply H1; apply (proj1 Hz).
    * rewrite negb_true_iff, <- not_true_iff_false; intro H3.
      rewrite negb_true_iff, <- not_true_iff_false in Hz; 
        apply (proj2 Hz); apply H2; apply H3.
  + rewrite Fset.mem_filter, Bool.andb_false_iff; right.
    unfold vars_of_pb, is_a_solved_var; simpl.
    rewrite Oset.eq_bool_refl.
    rewrite negb_false_iff, Bool.andb_true_iff, 2 negb_true_iff.
    rewrite set_of_variables_in_range_of_subst_unfold.
    rewrite Fset.mem_union, (variables_t_unfold _ (Var y)), Bool.orb_false_iff.
    repeat split.
    * apply var_not_in_apply_renaming_list; trivial.
    * rewrite Fset.singleton_spec, <- not_true_iff_false, Oset.eq_bool_true_iff; assumption.
    * rewrite <- not_true_iff_false; intro Hx.
      unfold set_of_variables_in_range_of_subst in Hx.
      rewrite map_map, Fset.mem_Union in Hx.
      destruct Hx as [s [Hs Hx]]; rewrite in_map_iff in Hs.
      destruct Hs as [[x1 t2] [Hs Ht]]; subst s; simpl in Hx.
      rewrite (var_not_in_apply_renaming_term _ _ x_diff_y) in Hx; discriminate Hx.
  + rewrite Fset.mem_filter.
    unfold vars_of_pb, is_a_solved_var; simpl solved_part; simpl unsolved_part.
    rewrite set_of_variables_in_eq_list_unfold, 3 Fset.mem_union, (variables_t_unfold _ (Var x)).
    rewrite Fset.singleton_spec, Oset.eq_bool_refl, Bool.andb_true_l.
    rewrite x_sigma; apply refl_equal.
- unfold psi2; simpl solved_part; simpl unsolved_part.
  rewrite (list_size_unfold _ (_ :: _)).
  rewrite list_size_eqt_meas2_power4_renaming.
  unfold substitution_to_eq_list.
  destruct (Fset.elements_add_2 FX (domain_of_subst FX sigma) x) as [l1 [l2 H]].
  + rewrite <- not_true_iff_false; find_var_in_dom.
    intros [[_x t] [_Hx Hx]]; simpl in _Hx; subst _x.
    apply (Oset.find_none _ _ _ x_sigma _ Hx).
  + replace (apply_subst 
               OX ((x, Var y)
                     :: map
                     (fun vv_sigma : variable dom * term =>
                        let (v, v_sigma) := vv_sigma in
                        (v, apply_subst OX ((x, Var y) :: nil) v_sigma))
                     sigma)) with
    (apply_subst OX (map
                       (fun vv_sigma : variable dom * term =>
                          let (v, v_sigma) := vv_sigma in
                          (v, apply_subst OX ((x, Var y) :: nil) v_sigma))
                       ((x, Var x) :: sigma)));
    [ | apply f_equal; simpl; rewrite Oset.eq_bool_refl; apply refl_equal].
    set (sigma' := (x, Var x) :: sigma) in *.
    rewrite (proj1 H).
    unfold domain_of_subst; simpl Fset.mk_set; rewrite map_map, map_fst.
    unfold domain_of_subst at 2 in H.
    rewrite (proj2 H), 2 map_app, (map_unfold _ (_ :: _)), 2 list_size_app, 
      (list_size_unfold _ (_ :: _)).
    rewrite 2 list_size_eqt_meas2_power4_subst_renaming.
    unfold sigma' at 2; simpl apply_subst at 2; rewrite Oset.eq_bool_refl.
    repeat rewrite plus_assoc; apply plus_le_compat; 
      [ | apply list_size_eqt_meas2_power4_subst_dec].
    rewrite plus_comm; repeat rewrite plus_assoc; apply plus_le_compat_l; 
      apply list_size_eqt_meas2_power4_subst_dec.
- (* 1/1 *)
  unfold psi3; apply Fset.cardinal_subset; rewrite Fset.subset_spec; intro z.
  rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  intros [Hz Kz]; split.
  + apply H1; apply Hz.
  + rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff in Kz.
    rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff; intro Jz; apply Kz.
    simpl; right; rewrite map_map.
    rewrite in_map_iff in Jz; destruct Jz as [[_z t] [_Jz Jz]]; simpl in _Jz; subst _z.
    rewrite in_map_iff; eexists; split; [ | apply Jz]; trivial.
Qed.

Lemma merge1_decreases :
 forall x g l2 l sigma x_val, 
   Oset.find OX x sigma = Some x_val -> size (Term g l2) < size x_val ->
   measure (mk_pb ((x, Term g l2) :: sigma) ((x_val, Term g l2) :: l)) <
   measure (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x g l2 l sigma x_val x_sigma L.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
unfold decomposition_step in *; simpl solved_part in *; simpl unsolved_part in *.
cbv iota beta zeta in H1, H2.
assert (Hst : Oset.eq_bool (OT OX OF) (Var x) (Term g l2) = false).
{
  rewrite <- not_true_iff_false, Oset.eq_bool_true_iff; discriminate.
}
rewrite Hst, x_sigma in H1, H2.
destruct x_val as [ | f l1]; 
  [simpl in L; generalize (le_S_n _ _ L); intro LL; inversion LL | ].
assert (LL := L); rewrite nat_compare_lt in LL; simpl in H1, H2, LL; rewrite LL in H1, H2.
rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le1_lt.
- unfold phi1; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intros z Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff in Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff; split.
  + apply H1; apply (proj1 Hz).
  + rewrite negb_true_iff, <- not_true_iff_false; intro H3.
    rewrite negb_true_iff, <- not_true_iff_false in Hz; apply (proj2 Hz); apply H2; apply H3.
- unfold psi2; simpl solved_part; simpl unsolved_part.
  rewrite 2 (list_size_unfold _ (_ :: _)).
  assert (Hx : In x ({{{domain_of_subst FX sigma}}})).
  {
    apply Fset.mem_in_elements; unfold domain_of_subst.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    exists (x, Term f l1); split; trivial.
    apply (Oset.find_some _ _ _ x_sigma).
  }
  assert (Hd : x addS domain_of_subst FX sigma =S= domain_of_subst FX sigma).
  {
    rewrite Fset.equal_spec; intro z; rewrite Fset.add_spec.
    case_eq (Oset.eq_bool OX z x); intro Hz; [ | apply refl_equal].
    rewrite Oset.eq_bool_true_iff in Hz; subst z.
    simpl; apply sym_eq; apply Fset.in_elements_mem; apply Hx.
  }
  unfold substitution_to_eq_list.
  rewrite domain_of_subst_unfold, (Fset.elements_spec1 _ _ _ Hd).
  destruct (in_split _ _ Hx) as [k1 [k2 Kx]]; rewrite Kx; clear Hx.
  assert (Hk : 
            forall k,
              list_size (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
                        (map
                           (fun x0 : variable dom =>
                              (Var x0,
                               apply_subst OX ((x, Term g l2) :: sigma) (Var x0))) k) <=
              list_size (fun st : term * term => let (s, t) := st in eqt_meas2 power4 s t)
                        (map
                           (fun x0 : variable dom =>
                              (Var x0, apply_subst OX sigma (Var x0))) k)).
  {
    intro k; induction k as [ | x1 k]; [apply le_n | ].
    rewrite 2 (map_unfold _ (_ :: _)), 2 (list_size_unfold _ (_ :: _)); 
      apply plus_le_compat; [simpl | apply IHk].
    case_eq (Oset.eq_bool OX x1 x); [ | intros; apply le_n].
    rewrite Oset.eq_bool_true_iff; intro; subst x1.
    rewrite x_sigma.
    apply lt_le_weak; apply eqt_meas2_strict_mon.
    rewrite nat_compare_lt; assumption.
  }
  rewrite 2 map_app, 2 (map_unfold _ (_ :: _)), 2 list_size_app, 2 (list_size_unfold _ (_ :: _)).
  simpl apply_subst at 2 5; rewrite Oset.eq_bool_refl, x_sigma.
  repeat rewrite plus_assoc; apply plus_lt_le_compat; [ | apply Hk].
  rewrite plus_comm; repeat rewrite <- plus_assoc; apply plus_lt_compat_l.
  rewrite plus_comm; repeat rewrite plus_assoc; apply plus_le_lt_compat.
  + apply plus_le_compat_l; apply Hk.
  + apply (merge_decr_aux2 x (lt_le_weak _ _ L)).
- unfold psi3; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intro z; rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  unfold vars_of_pb; simpl solved_part; simpl unsolved_part.
  intros [Hz Kz].
  split; 
    [ | rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff in Kz; simpl in Kz;
        rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff; simpl; 
        intro Jz; apply Kz; right; assumption].
  case_eq (z inS? variables_t FX (Term f l1)); intro Jz.
  + rewrite Fset.mem_union, Bool.orb_true_iff; right.
    unfold set_of_variables_in_eq_list, substitution_to_eq_list; rewrite map_map.
    rewrite Fset.mem_Union.
    eexists; split; [rewrite in_map_iff; exists x; split; [apply refl_equal | ] | ].
    * apply Fset.mem_in_elements; find_var_in_dom.
      exists (x, Term f l1); split; trivial.
      apply (Oset.find_some _ _ _ x_sigma).
    * simpl snd; rewrite Fset.mem_union, x_sigma, Jz, Bool.orb_true_r.
      apply refl_equal.
  + rewrite set_of_variables_in_eq_list_unfold, 3 Fset.mem_union, Jz, Bool.orb_false_l in Hz.
    case_eq (z inS? variables_t FX (Term g l2)); intro Lz.
    * rewrite set_of_variables_in_eq_list_unfold, 3 Fset.mem_union, Lz, Bool.orb_true_r.
      apply refl_equal.
    * rewrite Lz, Bool.orb_false_l in Hz.
      {
        case_eq (z inS? set_of_variables_in_eq_list l); intro Mz.
        - rewrite set_of_variables_in_eq_list_unfold, 3 Fset.mem_union, Mz, Bool.orb_true_r.
          apply refl_equal.
        - rewrite Mz, Bool.orb_false_l in Hz.
          unfold set_of_variables_in_eq_list, substitution_to_eq_list in Hz.
          rewrite map_map, Fset.mem_Union in Hz.
          destruct Hz as [s [Hs Hz]]; rewrite in_map_iff in Hs.
          destruct Hs as [v [Hs Hv]]; subst s; simpl in Hz.
          rewrite Fset.mem_union, Bool.orb_true_iff in Hz; destruct Hz as [Hz | Hz].
          + rewrite Fset.mem_union, Bool.orb_true_iff; right.
            unfold set_of_variables_in_eq_list, substitution_to_eq_list.
            rewrite map_map, Fset.mem_Union.
            eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ].
            * generalize (Fset.in_elements_mem _ _ _ Hv); clear Hv.
              find_var_in_dom; intros [[_v t] [_Hv Hv]]; simpl in _Hv; subst _v.
              apply Fset.mem_in_elements; 
                rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
              simpl in Hv; destruct Hv as [Hv | Hv]; [ | exists (v, t); split; trivial].
              simpl in Hv; injection Hv; clear Hv; do 2 intro; subst v t.
              exists (x, Term f l1); split; trivial.
              apply (Oset.find_some _ _ _ x_sigma).
            * simpl fst; rewrite Fset.mem_union, variables_t_unfold, Hz; apply refl_equal.
          + case_eq (Oset.eq_bool OX v x); intro Kv; rewrite Kv in Hz.
            * rewrite Lz in Hz; discriminate Hz.
            * rewrite Fset.mem_union, Bool.orb_true_iff; right.
              unfold set_of_variables_in_eq_list, substitution_to_eq_list.
              rewrite map_map, Fset.mem_Union.
              {
                eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ].
                - generalize (Fset.in_elements_mem _ _ _ Hv); clear Hv.
                  find_var_in_dom; intros [[_v t] [_Hv Hv]]; simpl in _Hv; subst _v.
                  apply Fset.mem_in_elements; 
                    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
                  simpl in Hv; destruct Hv as [Hv | Hv]; [ | exists (v, t); split; trivial].
                  simpl in Hv; injection Hv; clear Hv; do 2 intro; subst v t.
                  rewrite Oset.eq_bool_refl in Kv; discriminate Kv.
                - rewrite Fset.mem_union; simpl; rewrite Hz, Bool.orb_true_r.
                  apply refl_equal.
              }
      }
Qed.

Lemma merge2_decreases :
 forall x f l1 g l2 l sigma, 
  Oset.find OX x sigma = Some (Term f l1) -> size (Term g l2) >= size (Term f l1) ->
  measure (mk_pb sigma ((Term f l1, Term g l2) :: l)) < 
   measure (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x f l1 g l2 l sigma x_sigma L.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
assert (Hst : Oset.eq_bool (OT OX OF) (Var x) (Term g l2) = false).
{
  rewrite <- not_true_iff_false, Oset.eq_bool_true_iff; discriminate.
}
unfold decomposition_step in *; simpl solved_part in *; simpl unsolved_part in *.
cbv iota beta zeta in H1, H2; rewrite Hst, x_sigma in H1, H2.
assert (Aux :  match
           Oset.compare Onat (size (Term g l2)) (size (Term f l1))
         with
         | Eq =>
             Normal
               {|
               solved_part := sigma;
               unsolved_part := (Term f l1, Term g l2) :: l |}
         | Lt =>
             Normal
               {|
               solved_part := (x, Term g l2) :: sigma;
               unsolved_part := (Term f l1, Term g l2) :: l |}
         | Gt =>
             Normal
               {|
               solved_part := sigma;
               unsolved_part := (Term f l1, Term g l2) :: l |}
         end = Normal
               {|
               solved_part := sigma;
               unsolved_part := (Term f l1, Term g l2) :: l |}).
{
  rewrite Oset.compare_lt_gt.
  unfold ge in L; rewrite nat_compare_le in L; simpl in L; simpl.
  destruct (Nat.compare (list_size (size (symbol:=symbol)) l1)
        (list_size (size (symbol:=symbol)) l2)); trivial.
  apply False_rec; apply L; trivial.
}
rewrite Aux in H1, H2; clear Aux.
rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le1_lt.
- unfold phi1; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intros z Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff in Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff; split.
  + apply H1; apply (proj1 Hz).
  + rewrite negb_true_iff, <- not_true_iff_false; intro H3.
    rewrite negb_true_iff, <- not_true_iff_false in Hz; apply (proj2 Hz); apply H2; apply H3.
- unfold psi2; simpl solved_part; simpl unsolved_part.
  rewrite 2 (list_size_unfold _ (_ :: _)).
  do 2 apply plus_lt_compat_r.
  replace (eqt_meas2 power4 (Term f l1) (Term g l2)) with 
  (eqt_meas2 power4 (Term g l2) (Term f l1)).
  apply merge_decr_aux2; assumption.
  unfold eqt_meas2; rewrite size_common_comm; apply (f_equal (fun x => x + _)); apply plus_comm.
- unfold psi3; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intro z; rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  unfold vars_of_pb; simpl solved_part; simpl unsolved_part.
  intros [Hz Kz]; rewrite Fset.mem_union; split; [ | assumption].
  rewrite Fset.mem_union, Bool.orb_true_iff in Hz.
  destruct Hz as [Hz | Hz]; [ | rewrite Hz; apply Bool.orb_true_r].
  rewrite set_of_variables_in_eq_list_unfold, 2 Fset.mem_union, 2 Bool.orb_true_iff in Hz.
  unfold set_of_variables_in_eq_list, substitution_to_eq_list.
  destruct Hz as [[Hz | Hz] | Hz].
  + rewrite Bool.orb_true_iff; right.
    rewrite map_map, Fset.mem_Union.
    eexists; split; [rewrite in_map_iff; exists x; split; [apply refl_equal | ] | ].
    * apply Fset.mem_in_elements; find_var_in_dom.
      exists (x, Term f l1); split; trivial.
      apply (Oset.find_some _ _ _ x_sigma).
    * rewrite Fset.mem_union, Bool.orb_true_iff; right.
      simpl; rewrite x_sigma; assumption.
  + rewrite map_unfold, Fset.Union_unfold, 2 Fset.mem_union; simpl snd.
    rewrite Hz, Bool.orb_true_r; apply refl_equal.
  + rewrite map_unfold, Fset.Union_unfold, 2 Fset.mem_union.
    unfold set_of_variables_in_eq_list in Hz; rewrite Hz, Bool.orb_true_r; apply refl_equal.
Qed.

Lemma move_eq_decreases :
 forall x g l2 l sigma, Oset.find OX x sigma = None ->
  measure (mk_pb ((x, Term g l2) :: sigma) l) < measure (mk_pb sigma ((Var x, Term g l2) :: l)).
Proof.
intros x g l2 l sigma x_sigma.
assert (H1 := vars_of_pb_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
assert (H2 := is_a_solved_var_inv (mk_pb sigma ((Var x, Term g l2) :: l))).
assert (Hst : Oset.eq_bool (OT OX OF) (Var x) (Term g l2) = false).
{
  rewrite <- not_true_iff_false, Oset.eq_bool_true_iff; discriminate.
}
unfold decomposition_step in *; simpl solved_part in *; simpl unsolved_part in *.
cbv iota beta zeta in H1, H2; rewrite Hst, x_sigma in H1, H2; rewrite Fset.subset_spec in H1.
unfold measure; apply lex_le2_lt.
- unfold phi1; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intros z Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff in Hz.
  rewrite Fset.mem_filter, Bool.andb_true_iff; split.
  + apply H1; apply (proj1 Hz).
  + rewrite negb_true_iff, <- not_true_iff_false; intro H3.
    rewrite negb_true_iff, <- not_true_iff_false in Hz; apply (proj2 Hz); apply H2; apply H3.
- unfold psi2; simpl solved_part; simpl unsolved_part.
  rewrite (list_size_unfold _ (_ :: _)).
  rewrite <- plus_assoc, (plus_comm (eqt_meas2 _ _ _)), <- plus_assoc.
  apply plus_le_compat_l; rewrite plus_comm.
  unfold substitution_to_eq_list.
  rewrite domain_of_subst_unfold.
  assert (Hx : x inS? domain_of_subst FX sigma = false).
  {
    unfold domain_of_subst.
    rewrite <- not_true_iff_false, Fset.mem_mk_set, Oset.mem_bool_true_iff.
    intro Hx; rewrite in_map_iff in Hx.
    destruct Hx as [[_x t] [_Hx Hx]]; simpl in _Hx; subst _x.
    apply (Oset.find_none _ _ _ x_sigma _ Hx).
  }
  destruct (Fset.elements_add_2 _ _ x Hx) as [k1 [k2 [Hk Kk]]].
  rewrite Hk, Kk, 2 map_app, (map_unfold _ (_ :: _)), 2 list_size_app, 
    (list_size_unfold _ (_ :: _)).
  repeat rewrite plus_assoc; apply plus_le_compat; [rewrite plus_comm; apply plus_le_compat | ].
  + simpl; rewrite Oset.eq_bool_refl; apply le_n.
  + assert (Kx : ~ In x k1).
    {
      intro Kx; rewrite <- not_true_iff_false in Hx; apply Hx; apply Fset.in_elements_mem.
      rewrite Hk; apply in_or_app; left; assumption.
    }
    revert Kx; generalize k1; intro l1.
    induction l1 as [ | x1 l1]; intro Kx; [apply le_n | ].
    assert (Hx1 : Oset.eq_bool OX x1 x = false).
    {
      rewrite <- not_true_iff_false; rewrite Oset.eq_bool_true_iff; intro Hx1.
      apply Kx; left; assumption.
    }
    simpl; rewrite Hx1; apply plus_le_compat_l; apply IHl1.
    intro Kx1; apply Kx; right; assumption.
  + assert (Kx : ~ In x k2).
    {
      intro Kx; rewrite <- not_true_iff_false in Hx; apply Hx; apply Fset.in_elements_mem.
      rewrite Hk; apply in_or_app; right; assumption.
    }
    revert Kx; generalize k2; intro l1.
    induction l1 as [ | x1 l1]; intro Kx; [apply le_n | ].
    assert (Hx1 : Oset.eq_bool OX x1 x = false).
    {
      rewrite <- not_true_iff_false; rewrite Oset.eq_bool_true_iff; intro Hx1.
      apply Kx; left; assumption.
    }
    simpl; rewrite Hx1; apply plus_le_compat_l; apply IHl1.
    intro Kx1; apply Kx; right; assumption.
- unfold psi3; apply Fset.cardinal_strict_subset with x.
  + rewrite Fset.subset_spec; intro z; rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
    unfold vars_of_pb; simpl solved_part; simpl unsolved_part.
    intros [Hz Kz].
    case_eq (Oset.eq_bool OX z x); intro Hx; simpl in Kz; rewrite Hx in Kz; [discriminate Kz | ].
    find_not_var Hx; split; [ | assumption].
    case_eq (z inS? variables_t FX (Term g l2)); intro Jz; [trivial | ].
    case_eq (z inS? set_of_variables_in_eq_list l); intro Lz; [trivial | ].
    case_eq (z inS? set_of_variables_in_eq_list (substitution_to_eq_list sigma)); 
      intro Mz; [trivial | ].
    apply False_rec.
    revert Hz; rewrite Fset.mem_union, Lz, Bool.orb_false_l.
    revert Mz; unfold set_of_variables_in_eq_list, substitution_to_eq_list.
    rewrite <- not_true_iff_false, 2 map_map, 2 Fset.mem_Union.
    intros Mz Nz.
    destruct Nz as [s [Hs Nz]]; rewrite in_map_iff in Hs.
    destruct Hs as [v [Hs Hv]]; subst s.
    case_eq (Oset.eq_bool OX v x); intro Kv; [simpl in Nz; rewrite Kv in Nz | ].
    * rewrite Oset.eq_bool_true_iff in Kv; subst v.
      rewrite Fset.mem_union, Jz, Fset.singleton_spec, Hx in Nz; discriminate Nz.
    * apply Mz.
      {
        eexists; split; [rewrite in_map_iff; exists v; split; [apply refl_equal | ] | ].
        - apply Fset.mem_in_elements; find_var_in_dom.
          generalize (Fset.in_elements_mem _ _ _ Hv); find_var_in_dom; clear Hv.
          intros [[_v t] [_Hv Hv]]; simpl in _Hv; subst _v.
          destruct Hv as [Hv | Hv].
          + injection Hv; do 2 intro; subst; 
            rewrite Oset.eq_bool_refl in Kv; discriminate Kv.
          + exists (v, t); split; trivial.
        - simpl in Nz; rewrite Kv in Nz; simpl; apply Nz.
      }
  + rewrite Fset.mem_filter; simpl.
    rewrite Oset.eq_bool_refl, Bool.andb_false_r; apply refl_equal.
  + rewrite Fset.mem_filter; simpl; unfold vars_of_pb; simpl.
    rewrite Bool.andb_true_iff; split; [find_var_in_eq_list x | ].
    rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff.
    intro Hx; rewrite in_map_iff in Hx.
    destruct Hx as [[_x t] [_Hx Hx]]; simpl in _Hx; subst _x.
    apply (Oset.find_none _ _ _ x_sigma _ Hx).
Qed.

Lemma decomposition_decreases :
 forall f l1 l2 l sigma, length l1 = length l2 ->
   measure (mk_pb sigma (combine l l1 l2)) <
   measure (mk_pb sigma ((Term f l1, Term f l2) :: l)).
Proof.
intros f l1 l2 l sigma L.
assert (Hl : set_of_variables_in_eq_list (combine l l1 l2) =S= 
             (set_of_variables_in_eq_list ((Term f l1, Term f l2) :: l))).
{
  rewrite Fset.equal_spec; intro z.
  revert l2 l L; induction l1 as [ | t1 l1]; intros [ | t2 l2] l L; try discriminate L.
  - simpl combine; rewrite set_of_variables_in_eq_list_unfold, variables_t_unfold; simpl.
    rewrite 2 Fset.mem_union, Fset.empty_spec; apply refl_equal.
  - simpl in L; injection L; clear L; intro L.
    simpl combine; rewrite (IHl1 _ _ L); 
    repeat (rewrite set_of_variables_in_eq_list_unfold || 
                    rewrite (variables_t_unfold _ (Term _ _)) ||
                    rewrite Fset.mem_union || 
                    rewrite (map_unfold _ (_ :: _)) ||
                    rewrite (Fset.Union_unfold _ (_ :: _)) ||
                    rewrite Bool.orb_assoc).
    case (z inS? Fset.Union FX (map (variables_t FX) l1)); 
      [repeat rewrite Bool.orb_true_r; trivial | ].
    case (z inS? Fset.Union FX (map (variables_t FX) l2)); 
      [repeat rewrite Bool.orb_true_r; trivial | ].
    case (z inS? variables_t FX t1); [repeat rewrite Bool.orb_true_r; trivial | ].
    case (z inS? variables_t FX t2); [repeat rewrite Bool.orb_true_r; trivial | ].
    apply refl_equal.
}
apply lex_le1_lt.
- unfold phi1; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intro z; rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  unfold vars_of_pb; simpl solved_part; simpl unsolved_part.
  rewrite 2 Fset.mem_union, 2 Bool.orb_true_iff, (Fset.mem_eq_2 _ _ _ Hl).
  intros [Hz Kz]; split; [exact Hz | ].
  revert Kz; unfold is_a_solved_var; simpl solved_part; simpl unsolved_part.
  rewrite (Fset.mem_eq_2 _ _ _ Hl); exact (fun h => h).
- unfold psi2; simpl solved_part; simpl unsolved_part.
  apply plus_lt_compat_r.
  rewrite (list_size_unfold _ (_ :: _)).
  clear Hl; revert l2 l L; induction l1 as [ | t1 l1]; intros [ | t2 l2] l L; try discriminate L. 
  + simpl; apply le_n.
  + simpl in L; injection L; clear L; intro L.
    simpl.
    refine (lt_le_trans _ _ _ (IHl1 l2 _ L) _).
    rewrite list_size_unfold, plus_assoc; apply plus_le_compat_r.
    unfold eqt_meas2; rewrite 2 size_common_unfold; simpl size_common_list.
    rewrite 4 size_minus_unfold; simpl size_minus_list.
    rewrite plus_comm; repeat rewrite <- plus_assoc; apply plus_le_compat_l.
    repeat rewrite plus_assoc; apply plus_le_compat_r.
    repeat rewrite <- plus_assoc; rewrite (plus_comm _ (size_minus power4 t2 t1 + _)).
    repeat rewrite <- plus_assoc; apply plus_le_compat_l.
    rewrite (plus_comm 1 (plus _ _)), (plus_comm (size_minus_list power4 l2 l1) (plus _ _)).
    repeat rewrite <- plus_assoc; do 2 apply plus_le_compat_l.
    rewrite plus_comm; apply le_n.
- unfold psi3; apply Fset.cardinal_subset.
  rewrite Fset.subset_spec; intro z; rewrite 2 Fset.mem_filter, 2 Bool.andb_true_iff.
  unfold vars_of_pb; simpl solved_part; simpl unsolved_part.
  rewrite 2 Fset.mem_union, 2 Bool.orb_true_iff, (Fset.mem_eq_2 _ _ _ Hl).
  intros [Hz Kz]; split; trivial.
Qed.

Lemma meas_swapp_eq :
  forall s t l sigma, measure (mk_pb sigma ((s,t) :: l)) = measure (mk_pb sigma ((t,s) :: l)).
Proof.
intros s t l sigma; unfold measure; apply f_equal2; [apply f_equal2 | ].
- unfold phi1; rewrite 2 Fset.cardinal_spec; apply f_equal.
  apply Fset.elements_spec1; rewrite Fset.equal_spec; intro z.
  rewrite 2 Fset.mem_filter; apply f_equal2.
  + unfold vars_of_pb; simpl; rewrite 2 Fset.mem_union; apply f_equal2; [ | apply refl_equal].
    rewrite 2 set_of_variables_in_eq_list_unfold, 4 Fset.mem_union; 
      apply f_equal2; [apply Bool.orb_comm | apply refl_equal].
  + apply f_equal; unfold is_a_solved_var; simpl.
    destruct (Oset.find OX z sigma); trivial.
    apply f_equal2; [ | apply refl_equal].
    rewrite 2 set_of_variables_in_eq_list_unfold, 4 Fset.mem_union; 
      apply f_equal; apply f_equal2; [apply Bool.orb_comm | apply refl_equal].
- unfold psi2; apply f_equal2; [ | apply refl_equal].
  simpl; apply f_equal2; [ | apply refl_equal].
  unfold eqt_meas2; rewrite (plus_comm (size_minus power4 s t) (size_minus power4 t s));
  rewrite size_common_comm; apply f_equal.
  apply refl_equal.
- unfold psi3; rewrite 2 Fset.cardinal_spec; apply f_equal.
  apply Fset.elements_spec1; rewrite Fset.equal_spec; intro z.
  rewrite 2 Fset.mem_filter; apply f_equal2; [ | apply refl_equal].
  unfold vars_of_pb; simpl; rewrite 2 Fset.mem_union; apply f_equal2; [ | apply refl_equal].
  rewrite 2 set_of_variables_in_eq_list_unfold, 4 Fset.mem_union; 
    apply f_equal2; [apply Bool.orb_comm | apply refl_equal].
Qed.

Lemma decomposition_step_decreases :
  forall pb, 
   match decomposition_step pb with
  | Normal pb' => (measure pb') < (measure pb)
  | _ => True
  end.
Proof.
intros [sigma [ | [s t] l]]; simpl; trivial.
unfold decomposition_step; simpl unsolved_part; cbv iota beta.
case_eq (Oset.eq_bool (OT OX OF) s t); [intro s_eq_t | intro s_diff_t].
- (* 1/2 *)
  apply remove_trivial_eq_decreases; trivial.
- (* 1/1 *)
  destruct s as [ x | f l1 ]; destruct t as [ y | g l2].
  + (* 1/4 *)
    simpl solved_part.
    case_eq (Oset.find OX x sigma); [intros x_val x_sigma | intro x_sigma].
    * (* 1/5 *)
      rewrite (Oset.find_some_map _ _ _ _ x_sigma).
      apply coalesce1_decreases; [ | assumption].
      intro; subst y; rewrite Oset.eq_bool_refl in s_diff_t; discriminate s_diff_t.
    * (* 1/4 *)
      rewrite (Oset.find_none_map _ _ _ _ x_sigma).
      apply coalesce2_decreases; [ | assumption].
      rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in s_diff_t.
      intro; apply s_diff_t; subst; trivial.
  + (* 1/3 *)
    simpl solved_part; case_eq (Oset.find OX x sigma); 
    [intros [ y | f k]  x_sigma | intro x_sigma].
    * (* 1/5 *)
      exact I.
    * (* 1/4 *)
      {
        case_eq (Oset.compare Onat (size (Term g l2)) (size (Term f k))); intro L.
        - apply (merge2_decreases _ _ _ x_sigma).
          rewrite Oset.compare_lt_gt, CompOpp_iff in L; simpl in L.
          unfold ge; simpl; apply le_n_S; rewrite nat_compare_le, L; discriminate.
        - apply (merge1_decreases _ _ _ x_sigma).
          rewrite nat_compare_lt; apply L.
        - apply (merge2_decreases _ _ _ x_sigma).
          rewrite Oset.compare_lt_gt, CompOpp_iff in L; simpl in L.
          unfold ge; simpl; apply le_n_S; rewrite nat_compare_le, L; discriminate.
      }          
    * apply move_eq_decreases; trivial.
  + (* 1/2 *)
    simpl solved_part.
    case_eq (Oset.find OX y sigma); [intros y_val y_sigma | intro y_sigma].
    * (* 1/3 *) destruct y_val as [ | g l2]; [trivial | ].
      {
        case_eq (Oset.compare Onat (size (Term f l1)) (size (Term g l2))); intro L.
        - rewrite (meas_swapp_eq (Term f l1)).
          apply (merge2_decreases _ _ _ y_sigma).
          rewrite Oset.compare_lt_gt, CompOpp_iff in L; simpl in L.
          unfold ge; simpl; apply le_n_S; rewrite nat_compare_le, L; discriminate.
        - rewrite (meas_swapp_eq (Term f l1)).
          apply (merge1_decreases _ _ _ y_sigma).
          rewrite nat_compare_lt; apply L.
        - rewrite (meas_swapp_eq (Term f l1)).
          apply (merge2_decreases _ _ _ y_sigma).
          rewrite Oset.compare_lt_gt, CompOpp_iff in L; simpl in L.
          unfold ge; simpl; apply le_n_S; rewrite nat_compare_le, L; discriminate.
      }        
    * rewrite (meas_swapp_eq (Term f l1)); apply move_eq_decreases; trivial.
  + (* 1/1 *)
    case_eq (Oset.eq_bool OF f g); intro Hf; [ | trivial].
    rewrite Oset.eq_bool_true_iff in Hf; subst g.
    case_eq (Oset.eq_bool Onat (length l1) (length l2)); intro L; [ | trivial].
    simpl solved_part; apply decomposition_decreases.
    rewrite Oset.eq_bool_true_iff in L; assumption.
Qed.

Lemma decompose_completely_evaluates_aux :
 forall n l sigma, measure (mk_pb sigma l) <= n -> Inv_solved_part (mk_pb sigma l) -> 
 match decompose n (mk_pb sigma l) with
  | Some pb' =>  pb'.(unsolved_part) = nil 
  | None => True
end.
Proof.
unfold measure; intro n; induction n as [ | n]; intros l sigma H Inv_pb.
- simpl; destruct l as [ | [s t] l].
  + apply refl_equal.
  + inversion H.
    destruct (phi1 (mk_pb sigma ((s, t) :: l))) as [ | n1]; [ | discriminate].
    unfold psi2, eqt_meas2 in H1; simpl in H1.
    set (m := size_minus power4 s t + size_minus power4 t s + size_common s t) in *.
    assert (m_diff_zero : m <> 0).
    { 
      clear; unfold m.
      destruct s; destruct t; simpl.
      - discriminate.
      - discriminate.
      - do 2 rewrite <- plus_n_O.
        rewrite plus_comm; discriminate.
      - rewrite plus_comm; discriminate.
    }
    destruct m as [ | m].
    * apply False_rec; apply m_diff_zero; apply refl_equal.
    * discriminate.
- simpl; generalize (decomposition_step_decreases (mk_pb sigma l)); unfold measure.
  assert (Inv_pb' := Inv_solved_part_inv (mk_pb sigma l)).
  assert (Ok : forall pb'', decomposition_step (mk_pb sigma l) = Not_appliable pb'' -> 
                            pb''.(unsolved_part) = nil).
  {
    intros pb'' H'; destruct l as [ | [s t] l].
    - unfold decomposition_step in H'; simpl in H'; injection H'; intros; subst; apply refl_equal.
    - apply False_rec; revert H'; 
      unfold decomposition_step; simpl solved_part; simpl unsolved_part.
      cbv iota beta zeta.
      destruct (Oset.eq_bool (OT OX OF) s t).
      + intros H'; discriminate.
      + destruct s as [x | f l1]; destruct t as [y | g l2].
        * destruct (Oset.find 
                      OX x
                      (map
                         (fun vv_sigma : variable dom * term =>
                            let (v, v_sigma) := vv_sigma in
                            (v, apply_subst OX ((x, Var y) :: nil) v_sigma)) sigma));
          intros H';  discriminate.
        * { 
            assert (Hx := Inv_pb x); unfold is_a_solved_var in Hx; simpl in Hx.
            case_eq (Oset.find OX x sigma); 
              [intros [a | fx lx] x_sigma | intro x_sigma]; rewrite x_sigma in Hx.
            - rewrite Bool.andb_true_iff, negb_true_iff, set_of_variables_in_eq_list_unfold in Hx.
              destruct Hx as [Hx _]; rewrite <- not_true_iff_false in Hx; apply False_rec.
              apply Hx; find_var_in_eq_list x.
            - destruct (Oset.compare Onat (size (Term g l2)) (size (Term fx lx))); 
              discriminate.
            - discriminate.
          } 
        * assert (Hy := Inv_pb y); unfold is_a_solved_var in Hy; simpl in Hy.
          { 
            case_eq (Oset.find OX y sigma); 
            [intros [a | fy ly] y_sigma | intro y_sigma]; rewrite y_sigma in Hy.
            - rewrite Bool.andb_true_iff in Hy; destruct Hy as [Hy _].
              rewrite negb_true_iff, <- not_true_iff_false in Hy; intros _; apply Hy.
              find_var_in_eq_list y.
            - case (Oset.compare Onat (size (Term f l1)) (size (Term fy ly)));
              discriminate.
            - discriminate.
          } 
        * case (Oset.eq_bool OF f g); [ | discriminate].
          case (Oset.eq_bool Onat (length l1) (length l2)); discriminate.
  }
  case_eq (decomposition_step (mk_pb sigma l)).
  + intros [sigma' l'] K  H'; apply IHn.
    * apply le_S_n; refine (le_trans _ _ _ H' H).
    * rewrite K in Inv_pb'; apply Inv_pb'; assumption.
  + intros pb' H' _; apply Ok; assumption.
  + exact (fun _ _ => I).
Qed.

Lemma decompose_completely_evaluates :
 forall n l, measure (mk_pb nil l) <= n ->
 match decompose n (mk_pb nil l) with
  | Some pb' => 
     pb'.(unsolved_part) = nil /\ 
     (forall theta, is_a_solution (mk_pb nil l) theta <-> is_a_solution pb' theta)
  | None => forall theta, is_a_solution (mk_pb nil l) theta -> False
end.
Proof.
intros n l H.
assert (Inv_pb := Inv_solved_part_init l).
assert (H1 := decompose_is_sound n l nil).
assert (H2 := @decompose_is_complete n l nil).
assert (H3 := @decompose_completely_evaluates_aux n l nil H Inv_pb).
destruct (decompose n (mk_pb nil l)) as [[sigma' l'] | ].
split.
assumption.
intro theta; split; [apply H2 | apply H1].
assumption.
Qed.

Lemma rep_var_is_sound_and_complete :
  forall n sigma1 sigma2, 
    length sigma2 = n -> all_diff (map (@fst _ _) (sigma1 ++ sigma2)) ->
  match rep_var n sigma1 sigma2 with
  | Some sigma' => 
    forall tau, is_a_solution (mk_pb (sigma1 ++ sigma2) nil) tau <-> 
                is_a_solution (mk_pb sigma' nil) tau
  | None => forall tau, is_a_solution (mk_pb (sigma1 ++ sigma2) nil) tau -> False
  end.
Proof.
unfold is_a_solution; simpl.
intro n; induction n as [ | n]; intros sigma1 sigma2 L D; simpl.
(* 1/2 *)
- intro tau; split; exact (fun h => h).
(* 1/1 *)
- destruct sigma2 as [ | [x2 t2] sigma2]; [discriminate L | ].
  simpl in L; injection L; clear L; intro L.
  rewrite map_app, (map_unfold _ (_ :: _)) in D; simpl fst in D.
  assert (D' : all_diff (map (fst (B:=term)) (sigma1 ++ sigma2))).
  {
    rewrite <- all_diff_app_iff in D; rewrite map_app, <- all_diff_app_iff.
    destruct D as [D1 [D2 D]].
    rewrite all_diff_unfold in D2.
    destruct D2 as [Dx2 D2].
    split; [apply D1 | ].
    split; [apply D2 | ].
    intros a H1 H2; apply (D a H1).
    simpl; right; assumption.
  }
  assert (Dx2 : In x2 (map (@fst _ _) (sigma1 ++ sigma2)) -> False).
  {
    intro Hx2; rewrite in_map_iff in Hx2.
    destruct Hx2 as [[_x2 t] [_Hx2 Hx2]]; simpl in _Hx2; subst _x2.
    rewrite <- all_diff_app_iff in D.
    destruct (in_app_or _ _ _ Hx2) as [Kx2 | Kx2].
    - apply (proj2 (proj2 D) x2).
      + rewrite in_map_iff; exists (x2, t); split; trivial.
      + left; apply refl_equal.
    - assert (Dx2 := proj1 (proj2 D)).
      rewrite all_diff_unfold in Dx2.
      destruct Dx2 as [Dx2 _].
      refine (Dx2 _ _ (refl_equal _)).
      rewrite in_map_iff.
      exists (x2, t); split; trivial.
  }
  case_eq (x2 inS? variables_t FX t2); [intro x2_in_t2 | intro x2_not_in_t2].
  + (* 1/2 *)
    destruct t2 as [y2 | f2 l2].
    * (* 1/3 *)
      generalize (IHn sigma1 sigma2 L D'). 
      {
        case_eq (rep_var n sigma1 sigma2); [intros sigma'' Hsig' | intro Hsig'].
        - (* 1/4 *)
          intros H tau; split.
          + intros [H1 H2]; rewrite <- H; split; [apply H1 | ].
            intros x t H3; rewrite Oset.find_app in H3.
            case_eq (Oset.find OX x sigma1); [intros x_val x_sigma1 | intro x_sigma1];
            rewrite x_sigma1 in H3.
            * injection H3; clear H3; intro; subst t.
              apply H2; rewrite Oset.find_app, x_sigma1; trivial.
            * {
                case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
                - rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x. 
                  apply False_rec; apply Dx2.
                  rewrite in_map_iff.
                  exists (x2, t); split; trivial.
                  apply in_or_app; right; apply (Oset.find_some _ _ _ H3).
                - apply H2; rewrite Oset.find_app, x_sigma1; simpl.
                  rewrite x_diff_x2; assumption.
              }
          + rewrite <- H; intros [H1 H2]; split; [apply H1 | ].
            intros x t H3; rewrite Oset.find_app in H3.
            case_eq (Oset.find OX x sigma1); [intros x_val x_sigma1 | intro x_sigma1];
            rewrite x_sigma1 in H3.
            * injection H3; clear H3; intro; subst t.
              apply H2; rewrite Oset.find_app, x_sigma1; trivial.
            * {
                case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
                - rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x. 
                  simpl in H3; rewrite Oset.eq_bool_refl in H3; injection H3; clear H3;
                  intro; subst t.
                  rewrite in_variables_t_var in x2_in_t2; subst y2; apply refl_equal.
                - simpl in H3; rewrite x_diff_x2 in H3.
                  apply H2; rewrite Oset.find_app, x_sigma1; trivial.
              }
        - (* 1/3 *)
          intros H tau [H1 H2]; apply (H tau); split; [apply H1 | ].
          intros x t H3; rewrite Oset.find_app in H3.
          case_eq (Oset.find OX x sigma1); [intros x_val x_sigma1 | intro x_sigma1];
            rewrite x_sigma1 in H3.
            + injection H3; clear H3; intro; subst t.
              apply H2; rewrite Oset.find_app, x_sigma1; trivial.
            + case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
              * rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x. 
                apply False_rec; apply Dx2.
                rewrite in_map_iff.
                exists (x2, t); split; trivial.
                apply in_or_app; right; apply (Oset.find_some _ _ _ H3).
              * apply H2; rewrite Oset.find_app, x_sigma1; simpl.
                rewrite x_diff_x2; assumption.
      }
    * (* 1/2 *)
      intros tau [H1 H2].
      apply (lt_irrefl (size (apply_subst OX tau (Var x2)))).
      {
        rewrite (H2 x2 (Term f2 l2)) at 2.
        - destruct (var_in_subterm_pos FX x2 (Term f2 l2) x2_in_t2) as [[ | i p] Sub]; 
          [discriminate | ].
          assert (Sub' := subterm_at_pos_apply_subst_apply_subst_subterm_at_pos OX _ _ tau Sub).
          assert (H4 := size_subterm_at_pos (apply_subst OX tau (Term f2 l2)) i p); 
            rewrite Sub' in H4; exact H4.
        - rewrite Oset.find_app; simpl; rewrite Oset.eq_bool_refl.
          case_eq (Oset.find OX x2 sigma1); [ | intros; trivial].
          intros t H3; apply False_rec; apply Dx2.
          rewrite in_map_iff; exists (x2, t); split; trivial.
          apply in_or_app; left; apply (Oset.find_some _ _ _ H3).
      }
  + (* 1/1 *)
    set (sigma1' := ((x2, t2)
                       :: map
                       (fun xt : variable _ * term =>
                          let (x, t) := xt in (x, apply_subst OX ((x2, t2) :: nil) t))
                       sigma1)) in *.
    set (sigma2' := (map
                       (fun xt : variable _ * term =>
                          let (x, t) := xt in
                          (x, apply_subst OX ((x2, t2) :: nil) t)) sigma2)) in *.
    assert (L' : length sigma2' = n).
    {
      unfold sigma2'; rewrite map_length, L; apply refl_equal.
    }
    assert (D'' : all_diff (map (fst (B:=term)) (sigma1' ++ sigma2'))).
    {
      unfold sigma1', sigma2'.
      rewrite map_app, (map_unfold _ (_ :: _)), 2 map_map; simpl; rewrite <- map_app.
      case_eq (map
                 (fun x : variable dom * term =>
                    fst (let (x0, t) := x in (x0, apply_subst OX ((x2, t2) :: nil) t)))
                 (sigma1 ++ sigma2)); [trivial | ].
      intros x1 lx H; split.
      - rewrite <- H.
        intros a K Hx2; subst a; apply Dx2.
        simpl in K; rewrite in_map_iff in K.
        destruct K as [[_x2 _t2] [K2 K]]; simpl in K2; subst _x2.
        rewrite in_map_iff; eexists; split; [ | apply K]; trivial.
      - rewrite <- H.
        assert (all_diff_eq : 
                  forall (l1 l2 : list (variable dom)), all_diff l1 -> l1 = l2 -> all_diff l2);
          [intros; subst; assumption | ].
        apply (all_diff_eq _ _ D').
        rewrite <- map_eq; intros a _; destruct a; trivial.
    }
    assert (IH := IHn sigma1' sigma2' L' D'').
    case_eq (rep_var n sigma1' sigma2'); [intros sigma' Hsig | intros Hsig]; rewrite Hsig in IH.
    * (* 1/2 *)
      {
        intro tau; split.
        - (* 1/3 *)
          intros [H1 H2]; rewrite <- IH; split; [exact H1 | ].
          assert (Kx2 : apply_subst OX tau (Var x2) = apply_subst OX tau t2).
          {
            apply H2; rewrite Oset.find_app; simpl; rewrite Oset.eq_bool_refl.
            case_eq (Oset.find OX x2 sigma1); [ | intros; trivial].
            intros t H3; apply False_rec; apply Dx2.
            rewrite in_map_iff; exists (x2, t); split; trivial.
            apply in_or_app; left; apply (Oset.find_some _ _ _ H3).
          }
          intros x t H3; rewrite Oset.find_app in H3.
          case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
          + rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x. 
            unfold sigma1' in H3; simpl in H3.
            rewrite Oset.eq_bool_refl in H3; injection H3; clear H3; intro; subst t.
            apply Kx2.
          + case_eq (Oset.find OX x sigma1); [intros x_val x_sigma1 | intro x_sigma1].
            * unfold sigma1' in H3; simpl in H3.
              rewrite x_diff_x2, (Oset.find_some_map _ _ _ _ x_sigma1) in H3.
              injection H3; clear H3; intro; subst t.
              rewrite (H2 x x_val), (var_rep_aux tau x2 t2); trivial.
              rewrite Oset.find_app, x_sigma1; trivial.
            * unfold sigma1' in H3; simpl in H3.
              rewrite x_diff_x2, (Oset.find_none_map _ _ _ _ x_sigma1) in H3.
              {
                case_eq (Oset.find OX x sigma2); [intros x_val x_sigma2 | intro x_sigma2].
                - unfold sigma2' in H3; rewrite (Oset.find_some_map _ _ _ _ x_sigma2) in H3.
                  injection H3; clear H3; intro; subst t.
                  rewrite (H2 x x_val), (var_rep_aux tau x2 t2); trivial.
                  rewrite Oset.find_app, x_sigma1; simpl; rewrite x_diff_x2; trivial.
                - unfold sigma2' in H3; rewrite (Oset.find_none_map _ _ _ _ x_sigma2) in H3.
                  discriminate H3.
              }
        - (* 1/2 *)
          intros [H1 H2]; split; [exact H1 | ].
          assert (IH' :
                    (forall s t : term, False -> apply_subst OX tau s = apply_subst OX tau t) /\
                    (forall (x : variable dom) (x_val : term),
                       Oset.find OX x (sigma1' ++ sigma2') = Some x_val ->
                       match Oset.find OX x tau with
                         | Some v_sigma => v_sigma
                         | None => Var x
                       end = apply_subst OX tau x_val)).
          apply (proj2 (IH tau)); split; [apply H1 | apply H2].
          destruct IH' as [_ IH'].
          intros x x_val x_sigma.
          assert (Kx2 : apply_subst OX tau (Var x2) = apply_subst OX tau t2).
          {
            apply (IH' x2 t2).
            unfold sigma1'; rewrite Oset.find_app; simpl; rewrite Oset.eq_bool_refl; trivial.
          }
          case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
          + rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x.
            rewrite Oset.find_app in x_sigma; simpl in x_sigma; 
            rewrite Oset.eq_bool_refl in x_sigma.
            case_eq (Oset.find OX x2 sigma1); [intros _x_val x_sigma1 | intro x_sigma1].
            * apply False_rec; apply Dx2.
              rewrite in_map_iff; exists (x2, _x_val); split; trivial.
              apply in_or_app; left; apply (Oset.find_some _ _ _ x_sigma1).
            * rewrite x_sigma1 in x_sigma.
              injection x_sigma; clear x_sigma; intro; subst x_val.
              apply Kx2.
          + rewrite (var_rep_aux tau x2 t2); trivial; apply IH'.
            rewrite Oset.find_app in x_sigma; simpl in x_sigma; rewrite x_diff_x2 in x_sigma.
            unfold sigma1', sigma2'; simpl; rewrite x_diff_x2, Oset.find_app.
            case_eq (Oset.find OX x sigma1); [intros _x_val x_sigma1 | intro x_sigma1].
            * rewrite x_sigma1 in x_sigma; injection x_sigma; clear x_sigma; intro; subst _x_val.
              rewrite (Oset.find_some_map _ _ _ _ x_sigma1); trivial.
            * rewrite x_sigma1 in x_sigma.
              rewrite (Oset.find_none_map _ _ _ _ x_sigma1), (Oset.find_some_map _ _ _ _ x_sigma).
              trivial.
      }
    * intros tau [H1 H2]; apply (IH tau); split; [exact H1 | ].
      intros x x_val x_sigma.
      assert (Kx2 : apply_subst OX tau (Var x2) = apply_subst OX tau t2).
      {
        apply H2.
        rewrite Oset.find_app; simpl; rewrite Oset.eq_bool_refl.
        case_eq (Oset.find OX x2 sigma1); [intros _x_val x_sigma1 | intro x_sigma1; trivial].
        apply False_rec; apply Dx2.
        rewrite in_map_iff; exists (x2, _x_val); split; trivial.
        apply in_or_app; left; apply (Oset.find_some _ _ _ x_sigma1).
      }
      {
        case_eq (Oset.eq_bool OX x x2); [intro x_eq_x2 | intro x_diff_x2].
        - rewrite Oset.eq_bool_true_iff in x_eq_x2; subst x.
          rewrite Oset.find_app in x_sigma; simpl in x_sigma; 
          rewrite Oset.eq_bool_refl in x_sigma.
          injection x_sigma; clear x_sigma; intro; subst x_val.
          apply Kx2.
        - unfold sigma1', sigma2' in x_sigma; simpl in x_sigma.
          rewrite x_diff_x2, <- map_app in x_sigma.
          case_eq (Oset.find OX x (sigma1 ++ sigma2)); 
            [ intros t Hx 
            | intro Hx; rewrite (Oset.find_none_map _ _ _ _ Hx) in x_sigma; discriminate x_sigma].
          rewrite (Oset.find_some_map _ _ _ _ Hx) in x_sigma.
          injection x_sigma; clear x_sigma; intro; subst x_val.
          rewrite <- (var_rep_aux tau x2 t2); trivial; apply H2.
          rewrite Oset.find_app in Hx; simpl; rewrite Oset.find_app; simpl; rewrite x_diff_x2.
          apply Hx.
      }
Qed.

Lemma mgu_sound :
  forall l, 
  match mgu l with
  | Some mu =>  is_a_solution (mk_pb nil l) mu 
  | None => True
  end.
Proof.
intro l; unfold mgu.
assert (H := decompose_completely_evaluates l (le_n _)).
case_eq (decompose (measure (mk_pb nil l)) (mk_pb nil l)); [intros [tau l'] Hpb | intros; exact I].
rewrite Hpb in H; simpl in H; destruct H as [H1 H2]; subst l'; simpl.
case_eq (rep_var (length (clean_subst FX tau)) nil (clean_subst FX tau));
  [intros mu Hoc | intro Hoc; exact I ].
rewrite H2.
assert (H3 : all_diff (map (fst (B:=term)) (clean_subst FX tau))).
{
  unfold clean_subst; rewrite map_map, map_id; [ | intros; trivial].
  apply Fset.all_diff_elements.
}    
assert (H4 := rep_var_is_sound_and_complete nil (clean_subst FX tau) (refl_equal _) H3).
rewrite Hoc in H4.
assert (H5 : is_a_solution
                 {|
                   solved_part := nil ++ clean_subst FX tau;
                   unsolved_part := nil |} (clean_subst FX mu)).
{
  rewrite H4.
  unfold is_a_solution; simpl solved_part; simpl unsolved_part; split.
  - intros s t H; contradiction H.
  - intros x x_val H; rewrite 2 (clean_subst_eq FX); simpl; rewrite H.
    assert (Aux : forall n k2 k1 k, 
                    rep_var n k1 k2 = Some k -> length k2 <= n ->
                    (forall x1 t1 x t, In (x1, t1) k1 -> In (x, t) (k1 ++ k2) ->
                                       x1 inS? variables_t FX t = false) ->
                    (forall x1 t1 x t, In (x1, t1) k -> In (x, t) k ->
                                       x1 inS? variables_t FX t = false)).
    {
      intro n; induction n as [ | n]; intros [ | [x2 t2] k2] k1 k Hk L Hk1 x1 t1 y t K1 K.
      - simpl in Hk; injection Hk; clear Hk; rewrite <- app_nil_end; intro; subst k.
        rewrite <- app_nil_end in Hk1; apply (Hk1 _ _ _ _ K1 K).
      - simpl in L; inversion L.
      - simpl in Hk; injection Hk; clear Hk; intro; subst k.
        rewrite <- app_nil_end in Hk1; apply (Hk1 _ _ _ _ K1 K).
      - simpl in Hk.
        case_eq (x2 inS? variables_t FX t2); intro Hx2; rewrite Hx2 in Hk.
        + destruct t2 as [y2 | f2 l2]; [ | discriminate Hk].
          refine (IHn _ _ _ Hk _ _ _ _ _ _ K1 K).
          * simpl in L; apply (le_S_n _ _ L).
          * intros z1 s1 z2 s2 Ks1 Ks2; apply (Hk1 z1 s1 z2 s2 Ks1).
            destruct (in_app_or _ _ _ Ks2) as [Js2 | Js2];
              apply in_or_app; [left | do 2 right]; apply Js2.
        + assert (IH := IHn _ _ _ Hk).
          rewrite map_length in IH.
          generalize (IH (le_S_n _ _ L)); clear IH; intro IH.
          refine (IH _ _ _ _ _ K1 K).
          intros z1 s1 z2 s2 Ks1 Ks2.
          simpl in Ks1; destruct Ks1 as [Ks1 | Ks1]; 
          [injection Ks1; clear Ks1; do 2 intro; subst z1 s1 | ];
          (simpl in Ks2; destruct Ks2 as [Ks2 | Ks2];
          [injection Ks2; clear Ks2; do 2 intros; subst z2 s2 | ]).
          * trivial.
          * rewrite <- map_app, in_map_iff in Ks2; destruct Ks2 as [[_z2 _s2] [_Hz2 Ks2]].
            injection _Hz2; clear _Hz2; do 2 intro; subst _z2 s2.
            rewrite <- not_true_iff_false, var_in_apply_subst.
            intros [x' [Hx' Kx2]]; simpl in Kx2.
            {
              case_eq (Oset.eq_bool OX x' x2); [intro x'_eq_x2 | intro x'_diff_x2].
              - rewrite x'_eq_x2, Hx2 in Kx2; discriminate Kx2.
              - rewrite x'_diff_x2, in_variables_t_var in Kx2; subst x';
                rewrite Oset.eq_bool_refl in x'_diff_x2; discriminate x'_diff_x2.
            }
          * rewrite in_map_iff in Ks1; destruct Ks1 as [[_z1 _s1] [_Hz1 Ks1]].
            injection _Hz1; clear _Hz1; do 2 intro; subst _z1 s1.
            apply (Hk1 _ _ x2 t2 Ks1).
            apply in_or_app; right; left; apply refl_equal.
          * rewrite in_map_iff in Ks1; destruct Ks1 as [[_z1 _s1] [_Hz1 Ks1]].
            injection _Hz1; clear _Hz1; do 2 intro; subst _z1 s1.
            rewrite <- map_app, in_map_iff in Ks2; destruct Ks2 as [[_z2 _s2] [_Hz2 Ks2]].
            injection _Hz2; clear _Hz2; do 2 intro; subst _z2 s2.
            rewrite <- not_true_iff_false, var_in_apply_subst.
            intros [x' [Hx' Kx2]]; simpl in Kx2.
            {
              case_eq (Oset.eq_bool OX x' x2); [intro x'_eq_x2 | intro x'_diff_x2].
              - rewrite x'_eq_x2 in Kx2.
                assert (Abs := Hk1 _ _ x2 t2 Ks1).
                rewrite <- not_true_iff_false in Abs; apply Abs; [ | trivial].
                apply in_or_app; right; left; trivial.
              - rewrite x'_diff_x2, in_variables_t_var in Kx2; subst x'.
                assert (Abs := Hk1 _ _ z2 _s2 Ks1).
                rewrite <- not_true_iff_false in Abs; apply Abs; [ | trivial].
                destruct (in_app_or _ _ _ Ks2) as [Js2 | Js2];
                  apply in_or_app; [left | do 2 right]; trivial.
            }
    }
    assert (Aux' : forall (x1 : variable dom) (t1 : term) (y : variable dom) (t : term),
                     In (x1, t1) mu -> In (y, t) mu -> (x1 inS? variables_t FX t) = false).
    {
      apply (Aux _ _ _ _ Hoc (le_n _)).
      intros x1 t1 y t Abs; contradiction Abs.
    }
    apply sym_eq; apply (apply_subst_outside_dom FX).
    rewrite Fset.equal_spec; intro z; rewrite Fset.empty_spec, Fset.mem_inter.
    case_eq (z inS? domain_of_subst FX mu); intro Hz; [ | apply refl_equal].
    rewrite Bool.andb_true_l.
    unfold domain_of_subst in Hz; 
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Hz.
    destruct Hz as [[_z _t] [_Hz Hz]]; simpl in _Hz; subst _z.
    apply (Aux' z _t x x_val Hz (Oset.find_some _ _ _ H)).
}
unfold is_a_solution in H5; unfold is_a_solution; 
simpl solved_part in *; simpl unsolved_part in *; destruct H5 as [_ H5]; split.
- intros s t H; contradiction H.
- intros x x_val x_sigma.
  assert (K5 := H5 x x_val).
  rewrite 2 (clean_subst_eq FX) in K5.
  apply K5.
  rewrite find_clean_subst; assumption.
Qed.

Lemma mgu_complete :
  forall l, 
  match mgu l with
  | Some mu => 
     (forall theta, is_a_solution (mk_pb nil l) theta <-> 
     (exists sigma, forall x, apply_subst OX theta (Var x) = 
                              apply_subst OX sigma (apply_subst OX mu (Var x))))
  | None => forall theta, is_a_solution (mk_pb nil l) theta -> False
  end.
Proof.
intro l; unfold mgu.
assert (H := decompose_completely_evaluates l (le_n _)).
case_eq (decompose (measure (mk_pb nil l)) (mk_pb nil l)); [intros [tau l'] Hpb | intros Hpb].
- (* 1/2 *)
  rewrite Hpb in H; simpl in H; destruct H as [H1 H2]; subst l'; simpl.
  case_eq (rep_var (length (clean_subst FX tau)) nil (clean_subst FX  tau)); 
    [intros mu Hoc | intro Hoc ].
  + (* 1/3 *)
    assert (Hmu := mgu_sound l); 
    unfold mgu in Hmu; rewrite Hpb in Hmu; simpl in Hmu; rewrite Hoc in Hmu.
    intro theta; rewrite H2; split; intro H3.
    * (* 1/4 *)
      assert (H5 : is_a_solution {| solved_part := mu; unsolved_part := nil |} theta).
      {
        assert (H4 := rep_var_is_sound_and_complete nil (clean_subst FX tau) (refl_equal _)).
        rewrite Hoc in H4; rewrite <- H4; clear H4.
        unfold is_a_solution; split; [intros s t H; contradiction H | ].
        simpl solved_part; intros x t; rewrite find_clean_subst; apply (proj2 H3).
        unfold clean_subst; simpl; rewrite map_map, map_id; [ | intros; trivial].
        apply Fset.all_diff_elements.
      }
      exists theta; intro x.
      case_eq (Oset.find OX x mu); [ | intros; apply refl_equal].
      intros t Ht.
      generalize (proj2 H5 x t Ht); simpl solved_part; exact (fun h => h).
    * (* 1/3 *)
      destruct H3 as [sigma H3].
      split; [intros; contradiction | ].
      intros x t H; simpl in H.
      rewrite H2 in Hmu; assert (K := (proj2 Hmu) _ _ H).
      simpl; rewrite (H3 x).
      simpl in K; rewrite K.
      clear H K; pattern t; apply term_rec3; clear t; simpl; [intro; apply sym_eq; apply H3 | ].
      intros f k IH; simpl; apply f_equal; rewrite map_map, <- map_eq; apply IH.
  + (* 1/2 *)
    intros theta; rewrite H2; intro H3.
    assert (H4 := rep_var_is_sound_and_complete nil (clean_subst FX tau) (refl_equal _)).
    rewrite Hoc in H4; refine (H4 _ theta _).
    * simpl; unfold clean_subst; rewrite map_map, map_id; [ | intros; trivial].
      apply Fset.all_diff_elements.
    * unfold is_a_solution; split; [intros; contradiction | ].
      intros x t H; simpl in H.
      apply (proj2 H3); simpl.
      rewrite find_clean_subst in H; apply H.
- (* 1/1 *)
  rewrite Hpb in H; simpl in H; apply H.
Qed.

End Sec.
