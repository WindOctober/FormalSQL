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

Require Import Bool List Arith.
Require Import ListFacts FiniteSet OrderedSet Term Substitution.

Section Sec.
Hypothesis symbol : Type.
Hypothesis OF : Oset.Rcd symbol.

Hypothesis dom : Type.
Hypothesis OX : Oset.Rcd (variable dom).
Hypothesis X : Fset.Rcd OX.

Notation term := (term dom symbol).

Definition o_list_size (pb1 pb2 : list (term * term)) := 
    list_size (fun st => size (fst (B:=term) st)) pb1 < 
    list_size (fun st => size (fst (B:=term) st)) pb2. 

Lemma wf_size : well_founded o_list_size.
Proof.
unfold well_founded, o_list_size.
intros pb; apply Acc_intro.
generalize (list_size (fun st : term * term => size (fst st)) pb); clear pb. 
intro n; induction n as [ | n].
intros y Abs; absurd (list_size (fun st : term * term => size (fst st)) y < 0); 
auto with arith.
intros y Sy; inversion Sy; subst.
apply Acc_intro; intros x Sx; apply IHn; trivial.
apply IHn; trivial.
Defined.

Lemma matching_call1 :
  forall patt subj pb, o_list_size pb ((patt, subj) :: pb).
Proof.
intros patt sibj pb;
unfold o_list_size; simpl.
pattern (list_size (fun st : term * term => size (fst st)) pb); rewrite <- plus_O_n.
apply plus_lt_compat_r.
unfold lt; apply size_ge_one; trivial.
Qed.

Lemma matching_call2 :
  forall pat sub f lpat g lsub pb, 
     o_list_size ((pat,sub) :: nil) ((Term f (pat :: lpat), Term g (sub :: lsub)) :: pb).
Proof.
intros pat sub f lpat g lsub pb; unfold o_list_size; simpl.
auto with arith.
Qed.

Lemma matching_call3 :
  forall pat sub f lpat g lsub pb, 
     o_list_size ((Term f lpat, Term g lsub):: pb) ((Term f (pat :: lpat), Term g (sub :: lsub)) :: pb).
Proof.
intros pat sub f lpat g lsub pb; unfold o_list_size; simpl.
apply lt_n_S.
rewrite <- plus_assoc.
pattern (list_size (@size _ _) lpat + list_size (fun st : term * term => size (fst st)) pb);
rewrite <- plus_O_n.
apply plus_lt_compat_r.
unfold lt; apply size_ge_one; trivial.
Qed.

(** *** Definition of a step of matching. *)
Definition F_matching:
   forall pb (mrec : forall p, o_list_size p pb -> option (substitution dom symbol)),
   option (substitution dom symbol).
Proof.
intro pb; case pb; clear pb.
(* 1/2 the problem is trivial, i.e. has no equations *)
exact (fun _ => Some nil).
(* 1/1 the problem as at least one equation *)
intro ps; case ps; clear ps.
intro patt; case patt; clear patt.
(* 1/2 the first equation of the problem is of the form x = subj *)
intros x subj pb mrec.
exact (match mrec _ (matching_call1 (Var x) subj pb) with 
             | Some subst => Oset.merge OX (OT OX OF) ((x,subj) :: nil) subst
             | None => None
             end).
(* 1/1 the first equation of the problem has the form f l = subj *)
intros f lpatt subj; case subj; clear subj.
(* 1/2 the subject is a variable => No solution *)
exact (fun _ _ _ => None).
(* 1/1 the subject has the form g k *)
intros g lsubj.
case (Oset.eq_bool OF f g); [ | exact (fun _ _ => None)].
(* 1/1 f and g are equal => recursive call *)
intro pb.
case lpatt; clear lpatt.
(* 1/2 the pattern is a constant *)
case lsubj; clear lsubj.
(* 1/3 the subject is a constant => recursive call *)
intro mrec; exact (mrec _ (matching_call1 (Term f nil) (Term g nil) pb)).
(* 1/2 the suject is NOT a constant => No solution *)
exact (fun _ _ _ => None).
(* 1/1 the pattern is not a constant *)
intros patt1 lpatt; case lsubj; clear lsubj.
(* 1/2 the subject is a constant *)
exact (fun _ => None).
(* 1/1 the subject is not a constant *)
intros subj1 lsubj mrec.
exact (match mrec _ (matching_call2 patt1 subj1 f lpatt g lsubj pb) with
     | Some sigma1 =>
           match mrec _ (matching_call3 patt1 subj1 f lpatt g lsubj pb) with
           | Some sigma2 => Oset.merge OX (OT OX OF) sigma1 sigma2
           | None => None
           end
     | None => None
     end).
Defined.

(** *** Definition of matching. *)
Definition matching : list (term * term) -> option (substitution dom symbol) :=
Fix wf_size (fun l => option (substitution dom symbol)) F_matching.

(** *** A more practical equivalent definition of matching. *)
Lemma matching_unfold : 
  forall l : list (term * term), matching l = @F_matching l (fun y _ => matching y).
Proof.
intros lpb; unfold matching.
refine (Fix_eq _ _ _ _ lpb).
clear lpb; intros lpb _F G H.
unfold F_matching; destruct lpb as [ | [patt subj] lpb]; simpl; auto.
destruct patt as [x | f l]; destruct subj as [y | g m]; simpl; auto.
rewrite H; trivial.
rewrite H; trivial.
case (Oset.eq_bool OF f g); trivial.
destruct l as [ | pat lpat]; destruct m as [ | sub lsub]; trivial.
rewrite H; trivial.
rewrite H; trivial.
Qed.

Lemma matching_unfold2 : forall pb,
  matching pb =
  match pb with
   | nil => Some nil
   | (patt, subj) :: pb =>
        match patt with
        | Var x => 
               match matching pb with
               | Some subst => Oset.merge OX (OT OX OF) ((x,subj) :: nil) subst
               | None => None
               end
         | Term f l => 
             match subj with
               | Var _ => None
               | Term g m => 
                   if Oset.eq_bool OF f g
                  then
                      match l with
                      | nil =>
                          match m with
                          | nil => matching pb
                          | sub1 :: lsub => None
                          end
                      | pat1 :: lpat => 
                           match m with
                           | nil => None
                           | sub1 :: lsub => 
                             match (matching ((pat1, sub1) :: nil)) with
                              | Some subst1 => 
                                  match  (matching ((Term f lpat, Term g lsub) :: pb)) with
                                  | Some subst => Oset.merge OX (OT OX OF) subst1 subst
                                  | None => None
                                  end 
                              | None => None
                              end
                           end
                      end
                  else None
               end
         end
    end.
Proof.
intros pb; rewrite matching_unfold; unfold F_matching; simpl.
destruct pb as [ | [patt subj] pb]; trivial.
destruct patt as [ x | f l]; trivial.
destruct subj as [x | g m]; trivial.
case (Oset.eq_bool OF f g); trivial.
destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub]; trivial.
Qed.

Lemma matching_correct_aux :
  forall pb sigma, 
    matching pb = Some sigma ->
    ((forall v t1, In (v,t1) sigma <-> Oset.find OX v sigma = Some t1) /\
     (forall v p s, v inS (variables_t X p) -> In (p, s) pb -> Oset.find OX v sigma <> None) /\
     (forall v, Oset.find OX v sigma <> None -> 
                exists p, exists s, In (p,s) pb /\ v inS (variables_t X p)) /\
     (forall p s, In (p,s) pb -> apply_subst OX sigma p = s)).
Proof.
assert (change_hyp : 
          forall sigma, 
            (forall v t1, In (v,t1) sigma <-> Oset.find OX v sigma = Some t1)  ->
            (forall a1 a1' b1 c1, 
               In (a1,b1) sigma -> In (a1',c1) sigma -> Oset.eq_bool OX a1 a1' = true -> 
               Oset.eq_bool (OT OX OF) b1 c1 = true)).
{
  intros sigma H v v' t1 t2 H1 H2.
  rewrite 2 Oset.eq_bool_true_iff; intro; subst v'.
  rewrite H in H1, H2.
  rewrite H1 in H2; injection H2; exact (fun h => h).
}
intro pb; pattern pb; apply (well_founded_ind wf_size); clear pb.
intros [ | [patt subj] pb] IH sigma H; rewrite matching_unfold2 in H.
- injection H; clear H; intros; subst; repeat split; trivial;
  intros; try contradiction.
  simpl in H; discriminate.
- destruct patt as [ x | f l].
  + (* 1/2 the pattern is a variable *)
    assert (H' := IH _ (matching_call1 _ _ _)).
    destruct (matching pb) as [subst | ].
    * (* 1/3 the rest of the problem has subst as solution *)
      generalize (H' _ (refl_equal _)); clear H'; intros [IH1 [IH2 [IH4 IH3]]].
      assert (H' := Oset.merge_correct OX (OT OX OF) ((x,subj) :: nil) subst).
      rewrite H in H'; destruct H' as [H1 [H2 H3]].
      split.
      {
        (* 1/4 first invariant unicity *)
        intros v t1; split; intro Ht1.
        - assert (H'' := Oset.merge_inv OX (OT OX OF) ((x,subj) :: nil) subst).
          rewrite H in H''.
          case_eq (Oset.find OX v sigma).
          + intros t2 Ft2; apply f_equal; symmetry.
            rewrite <- (Oset.eq_bool_true_iff (OT OX OF)); apply H'' with v v.
            * intros w w' u1 u2 [wu1_eq_xs | wu1_in_nil] [wu2_eq_xs | wu2_in_nil]; 
              try contradiction.
              injection wu1_eq_xs; intros; subst; 
              injection wu2_eq_xs; intros; subst; trivial.
              apply Oset.eq_bool_refl.
            * apply change_hyp; assumption.
            * assumption.
            * apply (Oset.find_some OX _ _ Ft2).
            * apply Oset.eq_bool_refl.
          + intro F; apply False_rec.
            apply (Oset.find_none _ _ _ F _ Ht1).
        - apply (Oset.find_some OX _ _ Ht1).
      } 
      split.
      {
        (* 1/4 second invariant domain of solution *)
        intros v p s v_in_p [ps_eq_xsubj | ps_in_pb].
        - injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst; simpl; simpl in v_in_p.
          rewrite Fset.singleton_spec, Oset.eq_bool_true_iff in v_in_p; subst v.
          rewrite (H1 x s).
          + discriminate.
          + simpl; rewrite Oset.eq_bool_refl; apply refl_equal.
        - assert (K2 := IH2 v p s v_in_p ps_in_pb).
          case_eq (Oset.find OX v subst).
          + intros v_subst H'.
            destruct (H2 _ _ H') as [b' [H'' _]]; simpl; rewrite H''; discriminate.
          + intros H'; rewrite H' in K2; absurd (@None term = None); trivial.
      }
      split.
      {
        (* 1/4  third invariant domain of solution again *)
        intros v H'; simpl in H'; assert (H3v := H3 v).
        destruct (Oset.find OX v sigma) as [v_sigma | ]; 
          [ | apply False_rec; apply H'; apply refl_equal].
        destruct (H3v v_sigma (refl_equal _)) as [case1 | case2].
        - simpl in case1.
          case_eq (Oset.eq_bool OX v x); intro Hv; rewrite Hv in case1; [ | discriminate case1].
          rewrite Oset.eq_bool_true_iff in Hv; subst v.
          exists (Var x); exists subj; split.
          + left; apply refl_equal.
          + simpl; rewrite Fset.singleton_spec; apply Oset.eq_bool_refl.
        - destruct (IH4 v) as [p [s [ps_in_pb v_in_p]]].
          + rewrite (proj2 case2); discriminate.
          + exists p; exists s; split; trivial; right; trivial.
      }
      {
        (* 1/3  fourth invariant correctness *)
        intros p s [ps_eq_xsubj | ps_in_pb].
        - assert (K1 := H1 x subj).
          injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst; simpl.
          rewrite K1; trivial.
          simpl; rewrite Oset.eq_bool_refl; reflexivity.
        - assert (K2 : forall v, v inS variables_t X p -> Oset.find OX v subst <> None).
          {
            intros v v_in_p; apply IH2 with p s; trivial.
          } 
          assert (KK2 : forall v, v inS variables_t X p ->
                                  apply_subst OX subst (Var v) = apply_subst OX sigma (Var v)).
          {
            intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
            destruct (Oset.find OX v subst) as [v_subst | ];
              [ | intro Abs; apply False_rec; apply Abs; apply refl_equal].
            clear K2; intros _ K2; destruct (K2 _ (refl_equal _)) as [b [K3 K4]].
              rewrite K3.
              rewrite Oset.eq_bool_true_iff in K4; apply K4.
          }
          rewrite <- (IH3 _ _ ps_in_pb).
          symmetry.
          generalize KK2; clear s ps_in_pb K2 KK2; pattern p; apply term_rec3; clear p.
          + intros v KK2; apply KK2.
            simpl; rewrite Fset.singleton_spec; apply Oset.eq_bool_refl.
          + intros f l IHl KK2.
            assert (IHl' : forall t, In t l -> apply_subst OX subst t = apply_subst OX sigma t).
            {
              intros t t_in_l; apply IHl; trivial.
              intros v v_in_t; apply KK2.
              destruct (In_split _ _ t_in_l) as [l1 [l2 H']]; subst l.
              rewrite variables_t_unfold, Fset.mem_Union.
              exists (variables_t X t); split; [ | assumption].
              rewrite in_map_iff; exists t; split; trivial.
            } 
            simpl; apply (f_equal (fun l => Term f l)).
            rewrite <- map_eq; trivial.
      } 
    * (* 1/2 the rest of the problem has no solution *)
      discriminate.
  + (* 1/1 the pattern is a compound term Term f l *)
    destruct subj as [x | g m].
    * discriminate.
    * { (* 1/1 the subject is a compound term Term g l *)
        case_eq (Oset.eq_bool OF f g); intro Hf; rewrite Hf in H; [ | discriminate H].
        rewrite Oset.eq_bool_true_iff in Hf; subst g.
        (* 1/2 both terms have the same top symbol *)
        destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub].
        + (* 1/4 patt = Term f nil, subj = Term f nil *)
          destruct (IH _ (matching_call1 _ _ _) sigma H) as [H1 [H2 [H4 H3]]].
          split; trivial; split; [ | split].
          * { 
              intros v p s v_in_p [ps_eq_ff | ps_in_pb].
                - injection ps_eq_ff; intros; subst.
                  simpl in v_in_p; rewrite Fset.empty_spec in v_in_p; discriminate v_in_p.
                - apply H2 with p s; trivial.
              }
            * intros v H'; destruct (H4 _ H') as [p [s [ps_in_pb v_in_p]]].
              exists p; exists s; split; trivial; right; trivial.
            * {
                intros p s [ps_eq_ff | ps_in_pb].
                - injection ps_eq_ff; intros; subst; simpl; trivial.
                - apply H3; trivial.
              }
          + (* 1/3 patt = Term f nil, subj = Term f (sub1 :: lsub) *)
            discriminate.
          + (* 1/2 patt = Term f (pat1 :: lpat), subj = Term f nil *)
            discriminate.
          + (* 1/1 patt = Term f (pat1 :: lpat), subj = Term f (sub1 :: lsub) *)
            assert (H' := IH _ (matching_call2 pat1 sub1 f lpat f lsub pb)).
            destruct (matching ((pat1,sub1) :: nil)) as [subst1 | ].
            * (* 1/2 pat1 = sub1 has subst1 as solution *)
              generalize (H' _ (refl_equal _)); clear H'; intros [IH1 [IH2 [IH4 IH3]]].
              assert (H' := IH _ (matching_call3 pat1 sub1 f lpat f lsub pb)).
              destruct (matching ((Term f lpat, Term f lsub) :: pb)) as [subst | ].
              { (* 1/3 the rest of the problem has subst as solution *)
                generalize (H' _ (refl_equal _)); clear H'; intros [IH1' [IH2' [IH4' IH3']]].
                assert (H' := Oset.merge_correct OX (OT OX OF) subst1 subst).
                rewrite H in H'; destruct H' as [H1 [H2 H3]].
                split; [ | split; [ | split]].
                - (* 1/5 first invariant unicity *)
                  intros v t1; split; intro Ht1.
                  + assert (H'' := Oset.merge_inv OX (OT OX OF) subst1 subst).
                    rewrite H in H''.
                    case_eq (Oset.find OX v sigma);
                      [ | intro F; apply False_rec; apply (Oset.find_none _ _ _ F _ Ht1)].
                    intros t2 Ft2; apply f_equal; symmetry.
                    rewrite <- (Oset.eq_bool_true_iff (OT OX OF)).
                    apply H'' with v v.
                    * apply change_hyp; assumption.
                    * apply change_hyp; assumption.
                    * assumption.
                    * apply (Oset.find_some _ _ _ Ft2).
                    * apply Oset.eq_bool_refl.
                  + apply (Oset.find_some _ _ _ Ht1).
                - (* 1/4 second invariant domain of solution *)
                  intros v p s v_in_p [ps_eq_patsub | ps_in_pb].
                  + injection ps_eq_patsub; clear ps_eq_patsub; intros; subst; simpl.
                    rewrite variables_t_unfold, map_unfold, Fset.Union_unfold in v_in_p.
                    rewrite Fset.mem_union, Bool.orb_true_iff in v_in_p; 
                      destruct v_in_p as [v_in_pat1 | v_in_lpat].
                    * assert (K2 := IH2 v pat1 sub1 v_in_pat1 (or_introl _ (refl_equal _))).
                      case_eq (Oset.find OX v subst1); 
                        [ 
                        | intro H'; rewrite H' in K2; apply False_rec; apply K2; apply refl_equal].
                      intros v_subst H'.
                      rewrite (H1 _ _ H'); discriminate.
                    * assert (K2 := IH2' v (Term f lpat) (Term f lsub) 
                                         v_in_lpat (or_introl _ (refl_equal _))).
                      case_eq (Oset.find OX v subst); 
                        [ 
                        | intro H'; rewrite H' in K2; apply False_rec; apply K2; apply refl_equal].
                      intros v_subst H'.
                      destruct (H2 _ _ H') as [b [K3 _]]; rewrite K3; discriminate.
                  + assert (K2 := IH2' v p s v_in_p (or_intror _ ps_in_pb)).
                    case_eq (Oset.find OX v subst); 
                        [ 
                        | intro H'; rewrite H' in K2; apply False_rec; apply K2; apply refl_equal].
                    intros v_subst H'.
                    destruct (H2 _ _ H') as [b [K3 _]]; simpl; rewrite K3; discriminate.
                - (* 1/3 second invariant domain of solution *)
                  intros v H'; simpl in H'; assert (H3v := H3 v).
                  destruct (Oset.find OX v sigma) as [v_sigma | ];
                    [ | apply False_rec; apply H'; apply refl_equal].
                  destruct (H3v v_sigma (refl_equal _)) as [case1 | case2].
                  + destruct (IH4 v) as [p [s [ps_in_pb v_in_p]]].
                    * simpl; rewrite case1; discriminate.
                    * exists (Term f (pat1 :: lpat)); exists (Term f (sub1 :: lsub)); 
                        split; [left; trivial | ].
                         simpl in ps_in_pb; 
                               destruct ps_in_pb as [ps_eq_pat1sub1 | ps_in_nil];
                               [ | contradiction ps_in_nil].
                         injection ps_eq_pat1sub1; clear ps_eq_pat1sub1; intros; subst p s.
                         rewrite variables_t_unfold, map_unfold, Fset.Union_unfold.
                         rewrite Fset.mem_union, v_in_p; apply refl_equal.
                     + destruct (IH4' v) as [p [s [ps_in_pb v_in_p]]].
                       * simpl; rewrite (proj2 case2); discriminate.
                       * { 
                           destruct ps_in_pb as [ps_eq_patsub | ps_in_pb].
                           - exists (Term f (pat1 :: lpat)); exists (Term f (sub1 :: lsub)); split.
                             + left; trivial.
                             + injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
                               rewrite variables_t_unfold in v_in_p.
                               rewrite variables_t_unfold, map_unfold, Fset.Union_unfold.
                               rewrite Fset.mem_union, v_in_p, Bool.orb_true_r.
                               apply refl_equal.
                           - exists p; exists s; split; trivial; right; trivial.
                         }
                  - (* 1/4  third invariant correctness *)
                    intros p s [ps_eq_patsub | ps_in_pb].
                    + injection ps_eq_patsub; clear ps_eq_patsub; intros; subst; simpl.
                      replace (apply_subst OX sigma pat1) with sub1.
                      * apply (f_equal (fun l => Term f (sub1 :: l))).
                        assert (K := IH3' _ _ (or_introl _ (refl_equal _))).
                        simpl in K; injection K; clear K; intro K.
                        rewrite <- K; symmetry; rewrite <- map_eq.
                        intros p p_in_lpat; rewrite <- (apply_subst_eq_1 X).
                        assert (K2 : forall v, v inS variables_t X p -> 
                                               Oset.find OX v subst <> None).
                        {
                          intros v v_in_p; apply IH2' with (Term f lpat) (Term f lsub); trivial.
                          - rewrite variables_t_unfold, Fset.mem_Union.
                            exists (variables_t X p); split; trivial.
                            rewrite in_map_iff; exists p; split; trivial.
                          - left; trivial.
                        } 
                        intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
                        destruct (Oset.find OX v subst) as [v_subst | ];
                          [ | intro Abs; apply False_rec; apply Abs; apply refl_equal].
                        clear K2; intros _ K2.
                        destruct (K2 _ (refl_equal _)) as [b [K3 K4]]; rewrite K3;  trivial.
                        rewrite Oset.eq_bool_true_iff in K4; apply K4.
                      * assert (K := IH3 _ _ (or_introl _ (refl_equal _))).
                        rewrite <- K; symmetry.
                        rewrite <- (apply_subst_eq_1 X).
                        assert (K2 : forall v, v inS variables_t X pat1 -> 
                                               Oset.find OX v subst1 <> None).
                        {
                          intros v v_in_pat1; apply IH2 with pat1 sub1; trivial.
                          left; trivial.
                        } 
                        intros v v_in_pat1; generalize (K2 v v_in_pat1) (H1 v); simpl.
                        destruct (Oset.find OX v subst1) as [v_subst1 | ];
                          [ | intro Abs; apply False_rec; apply Abs; apply refl_equal].
                        clear K2; intros _ K2; rewrite (K2 _ (refl_equal _)); trivial.
                    + rewrite <- (IH3' _ _ (or_intror _ ps_in_pb)).
                      symmetry; rewrite <- (apply_subst_eq_1 X).
                      assert (K2 : forall v, v inS variables_t X p -> 
                                               Oset.find OX v subst <> None).
                      {
                        intros v v_in_p; apply IH2' with p s; trivial.
                        right; trivial.
                      } 
                      intros v v_in_p; generalize (K2 v v_in_p) (H2 v); simpl.
                      destruct (Oset.find OX v subst) as [v_subst | ];
                        [ | intro Abs; apply False_rec; apply Abs; apply refl_equal].
                      clear K2; intros _ K2; destruct (K2 _ (refl_equal _)) as [b [K3 K4]]; 
                      rewrite K3.
                      rewrite Oset.eq_bool_true_iff in K4; assumption.
              } 
              (* 1/3 the rest of the problem has subst as solution *)
              discriminate.
            * (* 1/2 pat1 = sub1 has no solution *)
              discriminate.
      }
Qed.

Lemma matching_correct :
  forall pb sigma, 
    matching pb = Some sigma ->
    ((forall v p s, v inS variables_t X p -> In (p, s) pb -> Oset.find OX v sigma <> None) /\
     (forall v, Oset.find OX v sigma <> None -> 
                exists p, exists s, In (p, s) pb /\ v inS variables_t X p) /\
     (forall p s, In (p, s) pb -> apply_subst OX sigma p = s)).
Proof.
intros pb sigma H; generalize (matching_correct_aux pb H); intuition.
Qed.

Lemma matching_complete :
  forall pb sigma, (forall p s, In (p,s) pb -> apply_subst OX sigma p = s) ->
  match matching pb with
    | Some tau => forall v p s, v inS variables_t X p -> In (p, s) pb -> 
                                apply_subst OX tau (Var v) = apply_subst OX sigma (Var v)
    | None => False
  end.
Proof.
intro pb; pattern pb; apply (well_founded_ind wf_size); clear pb.
intros [ | [patt subj] pb] IH sigma H;
rewrite matching_unfold2.
- intros; contradiction.
- assert (tailH : forall p s : term, In (p, s) pb -> apply_subst OX sigma p = s).
  {
    intros; apply H; right; assumption.
  }
  assert (Hsigma := IH _ (matching_call1 _ _ _) sigma tailH).
  {
    destruct patt as [ x | f l].
    - (* 1/2 the pattern is a variable *)
      case_eq (matching pb).
      + intros subst matching_pb_eq_subst; rewrite matching_pb_eq_subst in Hsigma.
        destruct (matching_correct_aux pb matching_pb_eq_subst) as [C1 [C2 [C4 C3]]].
        (* 1/3 the rest of the problem has subst as solution *)
        assert (H'' := Oset.merge_correct OX (OT OX OF) ((x,subj) :: nil) subst).
        case_eq (Oset.merge OX (OT OX OF) ((x, subj) :: nil) subst).
        * (* 1/4 the merging of substitutions succeeded *)
          intros tau matching_pb_eq_tau; rewrite matching_pb_eq_tau in H''.
          destruct H'' as [H1 [H2 H3]].
          {
            intros v p s v_in_p [ps_eq_xsubj | ps_in_pb].
            - injection ps_eq_xsubj; clear ps_eq_xsubj; intros; subst.
              rewrite variables_t_unfold, Fset.singleton_spec, Oset.eq_bool_true_iff in v_in_p; 
                subst v.
              rewrite (H (Var x) s (or_introl _ (refl_equal _))).
              simpl; rewrite (H1 x s); trivial.
              simpl; rewrite Oset.eq_bool_refl; apply refl_equal.
            - rewrite <- (Hsigma v p s v_in_p ps_in_pb).
              simpl; assert (K2 := C2 v p s v_in_p ps_in_pb).
              case_eq (Oset.find OX v subst);
                [ | intro F; rewrite F in K2; apply False_rec; apply K2; apply refl_equal].
              intros v_subst H''; destruct (H2 _ _ H'') as [b [K3 K4]]; simpl in K3; 
              rewrite K3; trivial.
              rewrite Oset.eq_bool_true_iff in K4; apply sym_eq; assumption.
          } 
        * (* 1/3  the merging of substitutions failed *)
          intro matching_pb_eq_none; rewrite matching_pb_eq_none in H''.
          destruct H'' as [v [v' [t1 [t2 [H1 [H2 [v_eq_v' t1_diff_t2]]]]]]]; simpl in v_eq_v'.
          rewrite Oset.eq_bool_true_iff in v_eq_v'; subst v'.
          rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in t1_diff_t2.
          rewrite C1 in H1; rewrite C1 in H2.
          { 
            case H1; clear H1; intro H1.
            - destruct (C4 v) as [p [s [ps_in_pb v_in_p]]].
              + rewrite H2; discriminate.
              + simpl in H1; case_eq (Oset.eq_bool OX v x); intro Hv; rewrite Hv in H1;
                [ | discriminate H1].
                injection H1; clear H1; intro; subst subj.
                rewrite Oset.eq_bool_true_iff in Hv; subst v.
                assert (Hv := Hsigma x p s v_in_p ps_in_pb).
                assert (Hv' := H (Var x) t1 (or_introl _ (refl_equal _))).
                rewrite Hv' in Hv; simpl in Hv; simpl in H2; rewrite H2 in Hv; 
                absurd (t2 = t1); assumption.
            - rewrite H1 in H2; apply t1_diff_t2; symmetry; injection H2; intro H3; exact H3.
          }
      + (* 1/2 the rest of the problem has no solution *)
        intro matching_pb_eq_none; rewrite matching_pb_eq_none in Hsigma.
        elim Hsigma.
    - (* 1/1 the pattern is a compound term Term f l *)
      destruct subj as [x | g m].
      + assert (H' := H (Term f l) (Var x) (or_introl _ (refl_equal _))); simpl in H'.
        discriminate.
      + (* 1/1 the subject is a compound term Term g l *)
        case_eq (Oset.eq_bool OF f g); [intro f_eq_g | intro f_diff_g].
        * (* 1/2 both terms have the same top symbol *)
          rewrite Oset.eq_bool_true_iff in f_eq_g; subst g.
          { 
            destruct l as [ | pat1 lpat]; destruct m as [ | sub1 lsub].
            - (* 1/5 patt = Term f nil, subj = Term f nil *)
              destruct (matching pb) as [tau | ]. 
              + intros v p s v_in_p [ps_eq_ff | ps_in_pb].
                * injection ps_eq_ff; intros; subst.
                  rewrite variables_t_unfold in v_in_p; simpl in v_in_p. 
                  rewrite Fset.empty_spec in v_in_p; discriminate v_in_p.
                * apply Hsigma with p s; trivial.
              + contradiction.
            - (* 1/4 patt = Term f nil, subj = Term f (sub1 :: lsub) *)
              assert (H' := H (Term f nil) (Term f (sub1 :: lsub)) (or_introl _ (refl_equal _)));
              simpl in H'.
              discriminate.
            - (* 1/3 patt = Term f (pat1 :: lpat), subj = Term f nil *)
              assert (H' := H (Term f (pat1 :: lpat)) (Term f nil) (or_introl _ (refl_equal _))); 
              simpl in H'.
              discriminate.
            - (* 1/2 patt = Term f (pat1 :: lpat), subj = Term f (sub1 :: lsub) *)
              assert (H' := IH _ (matching_call2 pat1 sub1 f lpat f lsub pb)).
              assert (Correct := matching_correct_aux ((pat1,sub1) :: nil)).
              case_eq (matching ((pat1,sub1) :: nil)).
              + (* 1/3 pat1 = sub1 has subst1 as solution *)
                intros subst1 matching_pat1sub1_eq_subst1.
                destruct (Correct _ matching_pat1sub1_eq_subst1) as  [C1 [C2 [C4 C3]]]; 
                  clear Correct.
                assert (H'' := IH _ (matching_call3 pat1 sub1 f lpat f lsub pb)).
                assert (Correct' := matching_correct_aux ((Term f lpat, Term f lsub) :: pb)).
                case_eq (matching ((Term f lpat, Term f lsub) :: pb)).
                * (* 1/4 the rest of the problem has subst as solution *)
                  intros subst matching_pb_eq_subst.
                  destruct (Correct' _ matching_pb_eq_subst) as  [C1' [C2' [C4' C3']]]; 
                    clear Correct'.
                  assert (H''' := Oset.merge_correct OX (OT OX OF) subst1 subst).
                  assert (headH : forall p s, In (p,s) ((pat1,sub1) :: nil) -> 
                                              apply_subst OX sigma p = s).
                  {
                    intros p s [ps_eq_pat1sub1 | ps_in_nil]; [idtac | contradiction].
                    injection ps_eq_pat1sub1; clear ps_eq_pat1sub1; intros; subst p s.
                    assert (K := H _ _ (or_introl _ (refl_equal _))).
                    simpl in K; injection K; intros; subst; trivial.
                  } 
                  assert (Hsigma1 := 
                            IH _ (matching_call2  pat1 sub1 f lpat f lsub pb) sigma headH).
                  rewrite matching_pat1sub1_eq_subst1 in Hsigma1.
                  clear tailH; 
                    assert (tailH : forall p s, In (p,s) ((Term f lpat, Term f lsub) :: pb) -> 
                                                apply_subst OX sigma p = s).
                  {
                    intros p s [ps_eq_patsub | ps_in_pb].
                    - injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
                      assert (K := H _ _ (or_introl _ (refl_equal _))).
                      simpl in K; injection K; intros; subst; trivial.
                    - apply H; right; trivial.
                  } 
                  clear Hsigma; 
                    assert (Hsigma := 
                              IH _ (matching_call3  pat1 sub1 f lpat f lsub pb) sigma tailH).
                  rewrite matching_pb_eq_subst in Hsigma.
                  { 
                    case_eq (Oset.merge OX (OT OX OF) subst1 subst).
                    - (* 1/5 the merging of substitutions succeeded *)
                      intros tau matching_pb_eq_tau; rewrite matching_pb_eq_tau in H'''.
                      destruct H''' as [H1 [H2 H3]].
                      intros v p s v_in_p [ps_eq_pat_sub | ps_in_pb].
                      + injection ps_eq_pat_sub; clear ps_eq_pat_sub; intros; subst p s.
                        rewrite variables_t_unfold, map_unfold, Fset.Union_unfold in v_in_p.
                        rewrite Fset.mem_union, Bool.orb_true_iff in v_in_p.
                        destruct v_in_p as [v_in_pat1 | v_in_lpat].
                        * rewrite <- (Hsigma1 v _ _ v_in_pat1 (or_introl _ (refl_equal _))).
                          simpl; assert (K2 := C2 v _ _ v_in_pat1 (or_introl _ (refl_equal _))).
                          { 
                            case_eq (Oset.find OX v subst1);
                            [ | intro F; rewrite F in K2; apply False_rec; apply K2; trivial].
                            intros v_subst1 H'''; rewrite (H1 _ _ H'''); trivial.
                          }
                        * assert (K := Hsigma v (Term f lpat) (Term f lsub)).
                          simpl in K; generalize (K v_in_lpat (or_introl _ (refl_equal _))); 
                          clear K; intro K.
                          simpl; assert (K2 := C2' v (Term f lpat) (Term f lsub)).
                          simpl in K2; generalize (K2 v_in_lpat (or_introl _ (refl_equal _))); 
                          clear K2; intro K2.
                            case_eq (Oset.find OX v subst);
                            [ | intro F; rewrite F in K2; apply False_rec; apply K2; trivial].
                            intros v_subst H'''; destruct (H2 _ _ H''') as [b [K3 K4]].
                            rewrite Oset.eq_bool_true_iff in K4; subst b.
                            rewrite H''' in K; rewrite K3; assumption.
                      + assert (K := Hsigma v p s v_in_p (or_intror _ ps_in_pb)).
                        simpl; assert (K2 := C2' v p s v_in_p (or_intror _ ps_in_pb)).
                        simpl in K; case_eq (Oset.find OX v subst);
                            [ | intro F; rewrite F in K2; apply False_rec; apply K2; trivial].
                        intros v_subst H'''; destruct (H2 _ _ H''') as [b [K3 K4]].
                        rewrite Oset.eq_bool_true_iff in K4; subst b.
                        rewrite H''' in K; rewrite K3; assumption.
                    - (* 1/4 the merging of substitutions failed *)
                      intro matching_pb_eq_none; rewrite matching_pb_eq_none in H'''.
                      destruct H''' as [v [v' [t1 [t2 [H1 [H2 [v_eq_v' t1_diff_t2]]]]]]].
                      rewrite Oset.eq_bool_true_iff in v_eq_v'; subst v'.
                      rewrite <- not_true_iff_false, Oset.eq_bool_true_iff in t1_diff_t2.
                      { 
                        case H1; clear H1; intro H1.
                        - destruct (C4 v) as [p [s [ps_in_pb v_in_p]]].
                          + simpl; rewrite H1; discriminate.
                          + assert (H1v := Hsigma1 v p s v_in_p ps_in_pb); simpl in H1v.
                            rewrite H1 in H1v.
                            destruct (C4' v) as [p' [s' [ps'_in_pb v_in_p']]].
                            * rewrite C1' in H2; rewrite H2; discriminate.
                            * assert (H2v := Hsigma v p' s' v_in_p' ps'_in_pb); simpl in H2v.
                              rewrite <- H2v in H1v.
                              rewrite C1' in H2; simpl in H2; rewrite H2 in H1v; 
                              apply t1_diff_t2; symmetry; assumption.
                        - apply t1_diff_t2; symmetry; 
                          rewrite C1' in H1; rewrite C1' in H2; rewrite H1 in H2; injection H2; 
                          intro H3; exact H3.
                      }
                  }
                * (* 1/3 the rest of the problem has no solution *)
                  intro matching_pb_eq_none; rewrite matching_pb_eq_none in H''.
                  apply (H'' sigma).
                  { intros p s [ps_eq_patsub | ps_in_pb].
                    - injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
                      assert (K := H _ _ (or_introl _ (refl_equal _))).
                      simpl in K; injection K; intros; subst; trivial.
                    - apply H; right; trivial.
                  }
              + (* 1/2 pat1 = sub1 has no solution *)
                intro matching_pb_eq_none; rewrite matching_pb_eq_none in H'.
                apply (H' sigma).
                intros p s [ps_eq_patsub | ps_in_pb].
                * injection ps_eq_patsub; clear ps_eq_patsub; intros; subst p s.
                  assert (K := H _ _ (or_introl _ (refl_equal _))).
                  simpl in K; injection K; intros; subst; trivial.
                * contradiction.
          }
        * { (* 1/1 the terms do not have the same top symbol *)
            absurd (f = g).
            - intro; subst g; rewrite Oset.eq_bool_refl in f_diff_g; discriminate f_diff_g.
            - assert (K := H _ _ (or_introl _ (refl_equal _))).
              simpl in K; injection K; intros; subst; trivial.
          } 
  }
Qed.

End Sec.

