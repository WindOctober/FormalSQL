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
        OrderedSet Partition FiniteSet FiniteBag FiniteCollection Join.
Require Import FTuples.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

(* *)
Lemma remove_dup_cols :
  forall l f s s2, s2 subS s -> (forall a, a inS s2 -> (f a) inS (Fset.diff _ s s2)) -> 
    (forall t, In t l -> labels T t =S= s) ->
    (forall t, In t l -> forall a, a inS s2 -> dot T t a = dot T t (f a)) ->
    forall t, labels T t =S= s -> (forall a, a inS s2 -> dot T t a = dot T t (f a)) ->
    Oeset.nb_occ 
      (OTuple T) (mk_tuple T (Fset.diff _ s s2) (dot T t)) 
      (map (fun x => (mk_tuple T (Fset.diff _ s s2) (dot T x))) l) = 
    Oeset.nb_occ (OTuple T) t l.
Proof.
intros l f s s2 Hs2 Hf Hl Kl t Ht Kt.
induction l as [ | t1 l]; [apply refl_equal | ].
simpl; apply f_equal2; [ | apply IHl; do 2 intro; [apply Hl | apply Kl]; right; assumption].
assert (Jt : (mk_tuple T (Fset.diff (A T) s s2) (dot T t)) =t=
                            (mk_tuple T (Fset.diff (A T) s s2) (dot T t1)) -> t =t= t1).
{
  intro Jt; rewrite tuple_eq in Jt; rewrite tuple_eq; split_tac.
  - rewrite (Fset.equal_eq_2 _ _ _ _ (Hl _ (or_introl _ (refl_equal _)))); apply Ht.
  - intros a Ha.
    case_eq (a inS? s2); intro Ha2.
    + rewrite Kt, (Kl _ (or_introl _ (refl_equal _))); trivial.
      assert (Ja := proj2 Jt (f a)).
      rewrite 2 dot_mk_tuple, (Hf a Ha2) in Ja; apply Ja.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); apply Hf; assumption.
    + assert (Ja := proj2 Jt a).
      rewrite 2 dot_mk_tuple, Fset.mem_diff, <- (Fset.mem_eq_2 _ _ _ Ht), Ha, Ha2 in Ja.
      simpl in Ja; apply Ja.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
      rewrite Fset.mem_diff, <- (Fset.mem_eq_2 _ _ _ Ht), Ha, Ha2; apply refl_equal.
}
case_eq (Oeset.compare (OTuple T) t t1); intro Ht1.
- rewrite (mk_tuple_eq _ (Fset.diff (A T) s s2) (Fset.diff (A T) s s2) (dot T t) (dot T t1)
             (Fset.equal_refl _ _)); [apply refl_equal | ].
  intros a Ha _; rewrite tuple_eq in Ht1; apply (proj2 Ht1).
  rewrite Fset.mem_diff, Bool.Bool.andb_true_iff in Ha.
  rewrite (Fset.mem_eq_2 _ _ _ Ht); apply (proj1 Ha).
- case_eq (Oeset.compare (OTuple T) (mk_tuple T (Fset.diff (A T) s s2) (dot T t))
                         (mk_tuple T (Fset.diff (A T) s s2) (dot T t1))); intro Kt1; trivial.
  rewrite (Jt Kt1) in Ht1; discriminate Ht1.
- case_eq (Oeset.compare (OTuple T) (mk_tuple T (Fset.diff (A T) s s2) (dot T t))
                         (mk_tuple T (Fset.diff (A T) s s2) (dot T t1))); intro Kt1; trivial.
  rewrite (Jt Kt1) in Ht1; discriminate Ht1.
Qed.

Lemma nb_occ_theta_join_list :
  forall f l1 l2 t, 
    Oeset.nb_occ (OTuple T) t (theta_join_list _ (join_tuple T) f l1 l2) =
    N.of_nat 
      (list_size 
         (fun t1 => 
            (match Oeset.compare (OTuple T) t1 (mk_tuple T (labels T t1) (dot T t)) with
               | Eq => 1 | _ => 0 end) * 
            list_size (fun t2 => 
                         if f t1 t2 
                         then match Oeset.compare (OTuple T) (join_tuple T t1 t2) t with
                                | Eq => 1 | _ => 0 end
                         else 0) l2)
         l1)%nat.
Proof.
intros f l1; induction l1 as [ | t1 l1]; intros l2 t; simpl; [apply refl_equal | ].
rewrite Oeset.nb_occ_app, IHl1, Nat2N.inj_add.
- apply f_equal2; [ | apply refl_equal].
  clear l1 IHl1.
  induction l2 as [ | t2 l2]; simpl.
  + rewrite Mult.mult_0_r; apply refl_equal.
  + rewrite d_join_list_cons; case_eq (f t1 t2); intro Hf; [ | simpl; apply IHl2].
    rewrite Oeset.nb_occ_unfold, IHl2, 2 Nat2N.inj_mul, Nat2N.inj_add.
    rewrite (Oeset.compare_lt_gt _ _ (join_tuple _ _ _)), N.mul_add_distr_l.
    apply f_equal2; [ | apply refl_equal].
    case_eq  (Oeset.compare (OTuple T) (join_tuple T t1 t2) t); intro Ht; simpl;
    [ | rewrite N.mul_0_r; trivial | rewrite N.mul_0_r; trivial].
    rewrite N.mul_1_r.
    assert (Ht' : t1 =t= (mk_tuple T (labels T t1) (dot T t))).
    {
      apply Oeset.compare_eq_sym.
      refine (Oeset.compare_eq_trans 
                _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ _ t1 t2 (Fset.equal_refl _ _))).
      apply mk_tuple_eq_2; intros.
      apply sym_eq; rewrite tuple_eq in Ht; apply (proj2 Ht).
      unfold join_tuple.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union, H.
      apply refl_equal.
    }
    rewrite Ht'; apply refl_equal.

Qed.

Definition natural_join_list s1 s2 := theta_join_list _ (join_tuple T) (join_compatible_tuple T) s1 s2. 

Lemma natural_join_list_brute_left_join_list :
  forall l1 l2 t,
    (forall t1 t2, Oeset.mem_bool (OTuple T) t1 l1 = true -> 
                   Oeset.mem_bool (OTuple T) t2 l2 = true ->
                   labels T t1 interS labels T t2 =S= emptysetS) ->
    Oeset.nb_occ (OTuple T) t (natural_join_list l1 l2) =
    Oeset.nb_occ (OTuple T) t (brute_left_join_list (tuple T) (join_tuple T) l1 l2).
Proof.
intros l1; unfold natural_join_list, brute_left_join_list, theta_join_list.
induction l1 as [ | x1 l1]; intros l2 t H; [apply refl_equal | ].
simpl; rewrite !Oeset.nb_occ_app; apply f_equal2.
- assert (H1 : forall t2, 
             Oeset.mem_bool (OTuple T) t2 l2 = true -> 
             (labels T x1 interS labels T t2) =S= (emptysetS)).
  {
    intro; apply H; simpl; rewrite Oeset.eq_bool_refl; apply refl_equal.
  }
  clear H; induction l2 as [ | x2 l2]; [apply refl_equal | ].
  unfold d_join_list; simpl.
  assert (Hx : join_compatible_tuple T x1 x2 = true).
  {
    rewrite join_compatible_tuple_alt.
    intros a Ha Ka.
    assert (Abs : a inS (Fset.empty (A T))).
    {
      assert (Aux : Oeset.mem_bool (OTuple T) x2 (x2 :: l2) = true).
      {
        simpl; rewrite Oeset.eq_bool_refl; apply refl_equal.
      }
      rewrite <- (Fset.mem_eq_2 _ _ _ (H1 _ Aux)), Fset.mem_inter, Ha, Ka; apply refl_equal.
    }
    rewrite Fset.empty_spec in Abs; discriminate Abs.
  }
  rewrite Hx; simpl; apply f_equal.
  apply IHl2; intros t2 Ht2; apply H1; simpl.
  rewrite Ht2, Bool.Bool.orb_true_r; apply refl_equal.
- apply IHl1. 
  intros t1 t2 Ht1; apply H; simpl.
  rewrite Ht1, Bool.Bool.orb_true_r; apply refl_equal.
Qed.

Lemma in_natural_join_list :
  forall l1 l2 x,
    In x (natural_join_list l1 l2) <->
    (exists x1 x2, In x1 l1 /\ In x2 l2 /\ join_compatible_tuple T x1 x2 = true /\
                   x = join_tuple T x1 x2).
Proof.
intros l1 l2; unfold natural_join_list; apply in_theta_join_list.
Qed.

Lemma natural_join_list_eq :
  forall l1 l2 l1' l2',
  (forall t1, Oeset.nb_occ (OTuple T) t1 l1 = Oeset.nb_occ (OTuple T) t1 l1') ->
  (forall t2, Oeset.nb_occ (OTuple T) t2 l2 = Oeset.nb_occ (OTuple T) t2 l2') ->
  forall t, Oeset.nb_occ (OTuple T) t (natural_join_list l1 l2) = 
            Oeset.nb_occ (OTuple T) t (natural_join_list l1' l2').
Proof.
intro l1; induction l1 as [ | u1 l1]; intros l2 l1' l2' H1 H2 t.
- assert (H1' : l1' = nil).
  {
    case_eq l1'; [intros; apply refl_equal | ].
    intros x1 k1 H.
    assert (Abs := H1 x1).
    rewrite H in Abs; simpl in Abs.
    rewrite Oeset.compare_eq_refl in Abs; simpl in Abs.
    destruct (Oeset.nb_occ (OTuple T) x1 k1);
    discriminate Abs.
  }
  rewrite H1'; simpl; apply refl_equal.
- assert (K1 := Oeset.nb_occ_permut _ _ _ H1).
  inversion K1; subst.
  assert (_H1 := fun x => Oeset.permut_nb_occ (OA := OTuple T) x H5).
  unfold natural_join_list in *.
  rewrite theta_join_list_app_1, ! (theta_join_list_unfold _ _ _ (_ :: _)), !flat_map_unfold.
  rewrite !Oeset.nb_occ_app.
  rewrite <- !theta_join_list_unfold, (IHl1 l2 (l0 ++ l3) l2' _H1 H2 t), 
    theta_join_list_app_1, Oeset.nb_occ_app.
  rewrite <- N.add_comm, <- N.add_assoc.
  apply f_equal.
  rewrite N.add_comm; apply f_equal2; [ | apply refl_equal].
  clear l1 IHl1 l0 l3 H1 K1 H5 _H1.
  revert l2' H2; induction l2 as [ | u2 l2]; intros l2' H2.
  + assert (H2' : l2' = nil).
    {
      case_eq l2'; [intros; apply refl_equal | ].
      intros x2 k2 H.
      assert (Abs := H2 x2).
      rewrite H in Abs; simpl in Abs.
      rewrite Oeset.compare_eq_refl in Abs; simpl in Abs.
      destruct (Oeset.nb_occ (OTuple T) x2 k2);
        discriminate Abs.
    }
    rewrite H2'; simpl; apply refl_equal.
  + assert (K2 := Oeset.nb_occ_permut _ _ _ H2).
    inversion K2; subst.
    assert (_H2 := fun x => Oeset.permut_nb_occ (OA := OTuple T) x H5).
    rewrite d_join_list_cons, d_join_list_app, d_join_list_cons, !Oeset.nb_occ_app.
    rewrite <- (join_compatible_tuple_eq _ _ _ _ _ H3 H1).
    case (join_compatible_tuple T u1 u2); simpl.
    * rewrite N.add_assoc, (N.add_comm _ (match Oeset.compare _ _ _ with Eq => 1 | _ => 0 end)).
     rewrite <- N.add_assoc; apply f_equal2.
     -- rewrite (Oeset.compare_eq_2 _ _ _ _ (join_tuple_eq _ _ _ _ _ H3 H1)); apply refl_equal.
     -- rewrite (IHl2 _ _H2), d_join_list_app, Oeset.nb_occ_app.
        apply refl_equal.
    * rewrite (IHl2 _ _H2), d_join_list_app, Oeset.nb_occ_app.
      apply refl_equal.
Qed.

Lemma nb_occ_natural_join_list :
  forall l1 l2 s1 s2,
    (forall t, In t l1 -> labels T t =S= s1) ->
    (forall t, In t l2 -> labels T t =S= s2) ->
    forall t, (Oeset.nb_occ (OTuple T) t (natural_join_list l1 l2) =
              (Oeset.nb_occ (OTuple T) (mk_tuple T s1 (dot T t)) l1) *
              (Oeset.nb_occ (OTuple T) (mk_tuple T s2 (dot T t)) l2) *
              (if labels T t =S?= (s1 unionS s2) then 1 else 0))%N.
Proof.
  intros l1 l2 s1 s2 H1 H2 t.
  unfold natural_join_list, theta_join_list.
  case_eq (labels T t =S?= (s1 unionS s2)); intro Ht.
  - rewrite N.mul_1_r.
    revert l2 H2; induction l1 as [ | t1 l1]; intros l2 H2; [apply refl_equal | simpl].
    assert (Hs1 := H1 t1 (or_introl _ (refl_equal _))).
    rewrite Oeset.nb_occ_app, N.mul_add_distr_r;
      apply f_equal2; [ | apply IHl1; intros; [apply H1; right | apply H2]; assumption].
    induction l2 as [ | t2 l2]; [rewrite N.mul_0_r; apply refl_equal | ].
    assert (Hs2 := H2 t2 (or_introl _ (refl_equal _))).
    assert (IH := IHl2 (fun t h => H2 t (or_intror _ h))).
    rewrite d_join_list_cons, (Oeset.nb_occ_unfold _ _ (_ :: _)), N.mul_add_distr_l, <- IH.
    case_eq (Oeset.compare (OTuple T) (mk_tuple T s1 (dot T t)) t1); intro Ht1.
    + rewrite N.mul_1_l.
      case_eq (Oeset.compare (OTuple T) (mk_tuple T s2 (dot T t)) t2); intro Ht2.
      * assert (H : join_compatible_tuple _ t1 t2 = true).
        {
          rewrite <- (join_compatible_tuple_eq _ _ _ _ _ Ht1 Ht2), join_compatible_tuple_alt.
          intros a Ha Ka; 
            rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha;
            rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ka.
          rewrite 2 dot_mk_tuple, Ha, Ka; apply refl_equal.
        }
        assert (H' : t =t= (join_tuple _ t1 t2)).
        {
          unfold join_tuple; rewrite tuple_eq, (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _));
            split_tac.
          - rewrite (Fset.equal_eq_1 _ _ _ _ Ht); apply Fset.union_eq.
            + rewrite (Fset.equal_eq_2 _ _ _ _ Hs1); apply Fset.equal_refl.
            + rewrite (Fset.equal_eq_2 _ _ _ _ Hs2); apply Fset.equal_refl.
          - intros a Ha; rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ H0), Ha.
            rewrite (Fset.mem_eq_2 _ _ _ H0), Fset.mem_union in Ha.
            case_eq (a inS? labels T t1); intro Ha1.
            + rewrite tuple_eq in Ht1; rewrite <- (proj2 Ht1).
              * rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ Hs1), Ha1; apply refl_equal.
              * rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), 
                  <- (Fset.mem_eq_2 _ _ _ Hs1); apply Ha1.
            + rewrite Ha1, Bool.Bool.orb_false_l in Ha.
              rewrite tuple_eq in Ht2; rewrite <- (proj2 Ht2).
              * rewrite dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ Hs2), Ha; apply refl_equal.
              * rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), 
                  <- (Fset.mem_eq_2 _ _ _ Hs2); apply Ha.
        }
        rewrite H, Oeset.nb_occ_unfold, H'; apply refl_equal.
      * case_eq (join_compatible_tuple _ t1 t2); intro H; trivial.
        rewrite join_compatible_tuple_alt in H.
        rewrite Oeset.nb_occ_unfold.
        case_eq (Oeset.compare (OTuple T) t (join_tuple _ t1 t2)); intro H'; trivial.
        assert (Abs : (mk_tuple T s2 (dot T t)) =t= t2).
        {
          rewrite tuple_eq in H'; unfold join_tuple in H'.
          rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
          (Fset.equal_eq_2 _ _ _ _ Hs2); split.
          - apply Fset.equal_refl.
          - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
            rewrite dot_mk_tuple, Ha.
            rewrite (proj2 H'), dot_mk_tuple, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs2), Ha.
            + rewrite Bool.Bool.orb_true_r.
              case_eq (a inS? labels T t1); intro Ha1; [ | apply refl_equal].
              rewrite H; trivial.
              rewrite (Fset.mem_eq_2 _ _ _ Hs2); assumption.
            + rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Ha.
              apply Bool.Bool.orb_true_r.
        }
        rewrite Abs in Ht2; discriminate Ht2.
      * case_eq (join_compatible_tuple _ t1 t2); intro H; trivial.
        rewrite join_compatible_tuple_alt in H.
        rewrite Oeset.nb_occ_unfold.
        case_eq (Oeset.compare (OTuple T) t (join_tuple _ t1 t2)); intro H'; trivial.
        assert (Abs : (mk_tuple T s2 (dot T t)) =t= t2).
        {
          rewrite tuple_eq in H'; unfold join_tuple in H'.
          rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
          (Fset.equal_eq_2 _ _ _ _ Hs2); split.
          - apply Fset.equal_refl.
          - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
            rewrite dot_mk_tuple, Ha.
            rewrite (proj2 H'), dot_mk_tuple, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs2), Ha.
            + rewrite Bool.Bool.orb_true_r.
              case_eq (a inS? labels T t1); intro Ha1; [ | apply refl_equal].
              rewrite H; trivial.
              rewrite (Fset.mem_eq_2 _ _ _ Hs2); assumption.
            + rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Ha.
              apply Bool.Bool.orb_true_r.
        }
        rewrite Abs in Ht2; discriminate Ht2.
    + rewrite N.mul_0_l; simpl.
      case_eq (join_compatible_tuple _ t1 t2); intro H; trivial.
      rewrite Oeset.nb_occ_unfold.
      case_eq (Oeset.compare (OTuple T) t (join_tuple _ t1 t2)); intro H'; trivial.
      assert (Abs : (mk_tuple T s1 (dot T t)) =t= t1).
      {
        rewrite tuple_eq in H'; unfold join_tuple in H'.
        rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
          (Fset.equal_eq_2 _ _ _ _ Hs1); split.
        - apply Fset.equal_refl.
        - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
          rewrite dot_mk_tuple, Ha.
          rewrite (proj2 H'), dot_mk_tuple, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), Ha; trivial.
          rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Ha; trivial.
      }
      rewrite Abs in Ht1; discriminate Ht1.
    + rewrite N.mul_0_l; simpl.
      case_eq (join_compatible_tuple _ t1 t2); intro H; trivial.
      rewrite Oeset.nb_occ_unfold.
      case_eq (Oeset.compare (OTuple T) t (join_tuple _ t1 t2)); intro H'; trivial.
      assert (Abs : (mk_tuple T s1 (dot T t)) =t= t1).
      {
        rewrite tuple_eq in H'; unfold join_tuple in H'.
        rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
          (Fset.equal_eq_2 _ _ _ _ Hs1); split.
        - apply Fset.equal_refl.
        - intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
          rewrite dot_mk_tuple, Ha.
          rewrite (proj2 H'), dot_mk_tuple, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), Ha; trivial.
          rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_union, Ha; trivial.
      }
      rewrite Abs in Ht1; discriminate Ht1.
  - rewrite N.mul_0_r.
    case_eq (Oeset.nb_occ 
               (OTuple T) t
               (flat_map (fun x1 => d_join_list (tuple T) (join_tuple _) (join_compatible_tuple _) x1 l2)
                         l1)); [trivial | ].
    intros p Hp.
    assert (H : Oeset.mem_bool 
                  (OTuple T) t (theta_join_list _ (join_tuple _) (join_compatible_tuple _) l1 l2) = true).
    {
      apply Oeset.nb_occ_mem; rewrite theta_join_list_unfold, Hp; discriminate.
    }
    rewrite Oeset.mem_bool_true_iff in H.
    destruct H as [t' [H H']].
    rewrite in_theta_join_list in H'.
    destruct H' as [t1 [t2 [Ht1 [Ht2 [_ H']]]]].
    rewrite H', tuple_eq in H; unfold join_tuple in H.
    rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)) in H.
    rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.union_eq _ _ _ _ _ (H1 _ Ht1) (H2 _ Ht2))), Ht in H.
    discriminate (proj1 H).
Qed.

Lemma nb_occ_natural_join_list_alt :
  forall l1 l2 s1 s2,
    (forall t, In t l1 -> labels T t =S= s1) ->
    (forall t, In t l2 -> labels T t =S= s2) ->
    s1 interS s2 =S= (emptysetS) ->
    forall t1 t2, labels T t1 =S= s1 -> labels T t2 =S= s2 ->
      (Oeset.nb_occ (OTuple T) (join_tuple _ t1 t2) (natural_join_list l1 l2) =
       (Oeset.nb_occ (OTuple T) t1 l1) *
       (Oeset.nb_occ (OTuple T) t2 l2))%N.
Proof.
intros l1 l2 s1 s2 Hl1 Hl2 Hs t1 t2 Ht1 Ht2.
rewrite (nb_occ_natural_join_list l1 l2 s1 s2); trivial.
unfold join_tuple at 3; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq _ _ _ _ _ Ht1 Ht2)).
rewrite Fset.equal_refl, N.mul_1_r.
apply f_equal2.
- apply Oeset.nb_occ_eq_1.
  rewrite tuple_eq, 
    (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), (Fset.equal_eq_2 _ _ _ _ Ht1),
    Fset.equal_refl.
  split; [apply refl_equal | ].
  intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  unfold join_tuple.
  rewrite 2 dot_mk_tuple, Ha, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Ht1), Ha.
  apply refl_equal.
- apply Oeset.nb_occ_eq_1.
  rewrite tuple_eq, 
    (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), (Fset.equal_eq_2 _ _ _ _ Ht2),
    Fset.equal_refl.
  split; [apply refl_equal | ].
  intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  unfold join_tuple.
  rewrite 2 dot_mk_tuple, Ha, Fset.mem_union, (Fset.mem_eq_2 _ _ _ Ht2), Ha.
  assert (Aux : a inS? labels T t1 = false).
  {
    rewrite <- not_true_iff_false, (Fset.mem_eq_2 _ _ _ Ht1); intro Ka.
    rewrite Fset.equal_spec in Hs.
    generalize (Hs a).
    rewrite Fset.mem_inter, Ha, Ka, Fset.empty_spec; discriminate.
  }
  rewrite Aux; apply refl_equal.
Qed.



Lemma rename_join :
  forall l1 l2 s1 s2 ss1 ss2, 
    Oset.permut (OAtt T) (map fst ss1) ({{{s1}}}) ->
    Oset.permut (OAtt T) (map fst ss2) ({{{s2}}}) ->
    (forall t, In t l1 -> labels T t =S= s1) ->
    (forall t, In t l2 -> labels T t =S= s2) ->
    let ss := 
          (ss1 ++ filter (fun x => negb (Oset.mem_bool (OAtt T) (fst x) (map fst ss1))) ss2) in
    let ss' := map (fun x => match x with (x1, x2) => (x2, x1) end) ss in
    let rho1 := apply_renaming _ ss1 in
    let rho2 := apply_renaming _ ss2 in
    let rho := apply_renaming _ ss in
    let rho' := apply_renaming _ ss' in
    all_diff (map fst ss1) -> all_diff (map fst ss2) -> all_diff (map snd (ss1 ++ ss2)) ->
    let f_join x := Fset.for_all (A T) 
                      (fun a => Oset.eq_bool (OVal T) (dot T x (rho1 a)) (dot T x (rho2 a))) 
                      (s1 interS s2) in
    forall t,
    Oeset.nb_occ (OTuple T) t (natural_join_list l1 l2) =
    Oeset.nb_occ 
      (OTuple T) t 
      (map (fun x => mk_tuple T (s1 unionS s2) (fun a => dot T x (rho a)))
           (filter f_join
                   (natural_join_list 
                      (map (rename_tuple _ rho1) l1) 
                      (map (rename_tuple _ rho2) l2)))).
Proof.
intros l1 l2 s1 s2 ss1 ss2 Hp1 Hp2 Hl1 Hl2 ss ss' rho1 rho2 rho rho' Hf1 Hf2 Hs f_join t.
assert (Hf : all_diff (map fst ss)).
{
  unfold ss; rewrite map_app, <- all_diff_app_iff.
  split; [assumption | ].
  split.
  - apply all_diff_map_filter; assumption.
  - intros a Ha Ka.
    rewrite in_map_iff in Ka; destruct Ka as [[_a b2] [_Ka Ka]].
    simpl in _Ka; subst _a.
    rewrite filter_In in Ka; simpl in Ka.
    rewrite <- (Oset.mem_bool_true_iff (OAtt T)) in Ha.
    rewrite Ha in Ka; discriminate (proj2 Ka).
}
assert (Hs' : all_diff (map snd ss)).
{
  rewrite map_app, <- all_diff_app_iff in Hs.
  unfold ss; rewrite map_app, <- all_diff_app_iff.
  split; [apply (proj1 Hs) | ].
  split.
  - apply all_diff_map_filter.
    apply (proj1 (proj2 Hs)).
  - intros a Ha Ka.
    rewrite in_map_iff in Ka; destruct Ka as [[b2 _a] [_Ka Ka]].
    simpl in _Ka; subst _a.
    rewrite filter_In in Ka; simpl in Ka.
    apply (proj2 (proj2 Hs) a Ha).
    rewrite in_map_iff; eexists; split; [ | apply (proj1 Ka)]; apply refl_equal.
}
assert (Hss : map fst ss = map snd ss').
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
assert (Hss' : map fst ss' = map snd ss).
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
rewrite map_app, <- all_diff_app_iff in Hs.
destruct Hs as [Hs1 [Hs2 Hs]].
rewrite (nb_occ_natural_join_list l1 l2 s1 s2 Hl1 Hl2).
assert (Hd : (Fset.map (A T) (A T) rho1 s1 interS Fset.map (A T) (A T) rho2 s2) =S= (emptysetS)).
{
  rewrite Fset.equal_spec; intro a; unfold Fset.map.
  rewrite Fset.mem_inter, Fset.empty_spec, 2 Fset.mem_mk_set.
  case_eq (Oset.mem_bool (OAtt T) a (map rho1 ({{{s1}}})));
    intro Ha1; [ | apply refl_equal].
  case_eq (Oset.mem_bool (OAtt T) a (map rho2 ({{{s2}}})));
    intro Ha2; [ | apply refl_equal].
  rewrite Oset.mem_bool_true_iff, in_map_iff in Ha1, Ha2.
  destruct Ha1 as [a1 [_Ha1 Ha1]].
  assert (Ka1 := Oset.in_permut_in _ Ha1 (Oset.permut_sym Hp1)).
  rewrite in_map_iff in Ka1; destruct Ka1 as [[_a1 b1] [_Ka1 Ka1]]; simpl in _Ka1; subst _a1.
  unfold rho1 in _Ha1; rewrite (apply_renaming_att _ ss1 Hf1 _ _ Ka1) in _Ha1; subst b1.
  destruct Ha2 as [a2 [_Ha2 Ha2]].
  assert (Ka2 := Oset.in_permut_in _ Ha2 (Oset.permut_sym Hp2)).
  rewrite in_map_iff in Ka2; destruct Ka2 as [[_a2 b2] [_Ka2 Ka2]]; simpl in _Ka2; subst _a2.
  unfold rho2 in _Ha2; rewrite (apply_renaming_att _ ss2 Hf2 _ _ Ka2) in _Ha2; subst b2.
  apply False_rec; apply (Hs a).
  - rewrite in_map_iff; eexists; split; [ | apply Ka1]; apply refl_equal.
  - rewrite in_map_iff; eexists; split; [ | apply Ka2]; apply refl_equal.
}
case_eq (labels T t =S?= (s1 unionS s2)); intro Ht;
  [rewrite N.mul_1_r | rewrite N.mul_0_r].
- set (t1 := mk_tuple T s1 (dot T t)).
  set (t2 := mk_tuple T s2 (dot T t)).
  assert (Hr1 : forall a1 a2, a1 inS s1 -> a2 inS s1 -> rho1 a1 = rho1 a2 -> a1 = a2).
  {
    intros a1 a2 Ha1 Ha2;
      apply (all_diff_one_to_one_apply_renaming _ _ _ _ Hf1 Hs1);
      refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp1));
        apply Fset.mem_in_elements; assumption.
  }
  assert (Hr2 : forall a1 a2, a1 inS s2 -> a2 inS s2 -> rho2 a1 = rho2 a2 -> a1 = a2).
  {
    intros a1 a2 Ha1 Ha2;
      apply (all_diff_one_to_one_apply_renaming _ _ _ _ Hf2 Hs2); 
        refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp2));
        apply Fset.mem_in_elements; assumption.
  }
  assert (Ht1 : Oeset.nb_occ (OTuple T) (rename_tuple _ rho1 t1) (map (rename_tuple _ rho1) l1) =
                Oeset.nb_occ (OTuple T) t1 l1).
  {
    apply (nb_occ_map_rename_tuple _ rho1 t1 l1).
    intros a1 a2 u2 Hu2 Ha1 Ha2; apply Hr1.
    - unfold t1 in Ha1; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha1.
      assumption.
    - rewrite Oeset.mem_bool_true_iff in Hu2.
      destruct Hu2 as [u2' [Hu2 Hu2']].
      rewrite tuple_eq in Hu2.
      rewrite <- (Fset.mem_eq_2 _ _ _ (Hl1 _ Hu2')), <- (Fset.mem_eq_2 _ _ _ (proj1 Hu2)).
      assumption.
  }
  assert (Ht2 : Oeset.nb_occ (OTuple T) (rename_tuple _ rho2 t2) (map (rename_tuple _ rho2) l2) =
                Oeset.nb_occ (OTuple T) t2 l2).
  {
    apply (nb_occ_map_rename_tuple _ rho2 t2 l2).
    intros a1 a2 u2 Hu2 Ha1 Ha2; apply Hr2.
    - unfold t2 in Ha1; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha1.
      assumption.
    - rewrite Oeset.mem_bool_true_iff in Hu2.
      destruct Hu2 as [u2' [Hu2 Hu2']].
      rewrite tuple_eq in Hu2.
      rewrite <- (Fset.mem_eq_2 _ _ _ (Hl2 _ Hu2')), <- (Fset.mem_eq_2 _ _ _ (proj1 Hu2)).
      assumption.
  }
  rewrite <- Ht1, <- Ht2.
  set (u1 := rename_tuple _ rho1 t1) in *.
  set (u2 := rename_tuple _ rho2 t2) in *.
  assert (Hu : Oeset.nb_occ 
                 (OTuple T) (join_tuple _ u1 u2)
                 (natural_join_list (map (rename_tuple _ rho1) l1) (map (rename_tuple _ rho2) l2)) = 
               (Oeset.nb_occ (OTuple T) u1 (map (rename_tuple _ rho1) l1) *
                Oeset.nb_occ (OTuple T) u2 (map (rename_tuple _ rho2) l2))%N).
  {
    apply (nb_occ_natural_join_list_alt _ _ (Fset.map (A T) (A T) rho1 s1)
                                           (Fset.map (A T) (A T) rho2 s2)).
    - intros x Hx; rewrite in_map_iff in Hx.
      destruct Hx as [y [_Hx Hx]]; subst x.
      rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 (rename_tuple_ok _ rho1 y))).      
      apply Fset.equal_refl_alt; unfold Fset.map.
      rewrite (Fset.elements_spec1 _ _ _ (Hl1 _ Hx)); apply refl_equal.
    - intros x Hx; rewrite in_map_iff in Hx.
      destruct Hx as [y [_Hx Hx]]; subst x.
      rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 (rename_tuple_ok _ rho2 y))).      
      apply Fset.equal_refl_alt; unfold Fset.map.
      rewrite (Fset.elements_spec1 _ _ _ (Hl2 _ Hx)); apply refl_equal.
    - apply Hd.
    - unfold u1.
      rewrite (Fset.equal_eq_1 _ _ _  _ (proj1 (rename_tuple_ok _ _ _))).
      unfold Fset.map, t1; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.equal_refl.
    - unfold u2.
      rewrite (Fset.equal_eq_1 _ _ _  _ (proj1 (rename_tuple_ok _ _ _))).
      unfold Fset.map, t2; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.equal_refl.
  }
  rewrite <- Hu.
  set (u := join_tuple _ u1 u2) in *.
  assert (Hfu : f_join u = true).
  {
    unfold f_join; rewrite Fset.for_all_spec, forallb_forall.
    intros a Ha; assert (Ka := Fset.in_elements_mem _ _ _ Ha).
    rewrite Oset.eq_bool_true_iff.
    unfold u, join_tuple, u1, u2; rewrite 2 dot_mk_tuple, 2 Fset.mem_union.
    assert (H1 : rho1 a inS labels T (rename_tuple _ rho1 t1)).
    {
      rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ rho1 t1))).
      unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
      exists a; split; [apply refl_equal | ].
      unfold t1; apply Fset.mem_in_elements; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
      rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ka; apply (proj1 Ka).
    }
    assert (H2 : rho2 a inS labels T (rename_tuple _ rho2 t2)).
    {
      rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ rho2 t2))).
      unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
      exists a; split; [apply refl_equal | ].
      unfold t2; apply Fset.mem_in_elements; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
      rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ka; apply (proj2 Ka).
    }
    assert (H2' : rho2 a inS? labels T (rename_tuple _ rho1 t1) = false).
    {
      case_eq (rho2 a inS? labels T (rename_tuple _ rho1 t1)); [ | intros; apply refl_equal].
      intro H2'.
      rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ rho2 t2))) in H2.
      rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ rho1 t1))) in H2'.
      unfold Fset.map, t1, t2 in H2, H2'.
      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in H2.
      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in H2'.
      rewrite Fset.equal_spec in Hd.
      assert (H := Hd (rho2 a)); unfold Fset.map in H.
      rewrite Fset.mem_inter, H2, H2', Fset.empty_spec in H.
      apply H.
    }
    rewrite H1, H2, H2'; simpl.
    rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ka.
    unfold rho1, rho2.
    rewrite (dot_rename_tuple_apply_renaming _ ss1 Hf1 Hs1 t1) with a (apply_renaming _ ss1 a),
            (dot_rename_tuple_apply_renaming _ ss2 Hf2 Hs2 t2) with a (apply_renaming _ ss2 a).
    - unfold t1, t2; rewrite 2 dot_mk_tuple, (proj1 Ka), (proj2 Ka); apply refl_equal.
    - unfold t2; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
      rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.permut_elements_mk_set_alt _ _ Hp2)).
      apply Fset.equal_refl.
    - assert (Ja := Fset.mem_in_elements _ _ _ (proj2 Ka)).
      generalize (Oset.in_permut_in a Ja (Oset.permut_sym Hp2)).
      rewrite in_map_iff; intros [[_a b] [_La La]]; simpl in _La; subst _a.
      rewrite (apply_renaming_att _ ss2 Hf2 _ _ La); assumption.
    - unfold t1; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
      rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.permut_elements_mk_set_alt _ _ Hp1)).
      apply Fset.equal_refl.
    - assert (Ja := Fset.mem_in_elements _ _ _ (proj1 Ka)).
      generalize (Oset.in_permut_in a Ja (Oset.permut_sym Hp1)).
      rewrite in_map_iff; intros [[_a b] [_La La]]; simpl in _La; subst _a.
      rewrite (apply_renaming_att _ ss1 Hf1 _ _ La); assumption.
  }    
  set (s := (Fset.map (A T) (A T) rho1 s1 unionS Fset.map (A T) (A T) rho2 s2)).
  assert (Ku : labels T u =S= s).
  {
    unfold u, join_tuple, s.
    rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)); apply Fset.union_eq.
    - unfold u1.
      rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 (rename_tuple_ok _ _ _))).
      unfold t1, Fset.map.
      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.equal_refl.
    - unfold u2.
      rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 (rename_tuple_ok _ _ _))).
      unfold t2, Fset.map.
      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.equal_refl.
  }
  set (_s2 := Fset.map (A T) (A T) rho2 (s1 interS s2)).
  assert (_Hs2 : _s2 subS s).
  {
    rewrite Fset.subset_spec; intro a; unfold _s2, s, Fset.map.
    rewrite Fset.mem_union, 3 Fset.mem_mk_set, Bool.Bool.orb_true_iff.
    intro Ha; right; revert Ha.
    rewrite 2 Oset.mem_bool_true_iff, in_map_iff.
    intros [b [_Ha Hb]]; rewrite in_map_iff.
    exists b; split; [assumption | ].
    apply Fset.mem_in_elements.
    generalize (Fset.in_elements_mem _ _ _ Hb); rewrite Fset.mem_inter, Bool.Bool.andb_true_iff.
    apply proj2.
  }
  assert (Aux : forall a1, a1 inS Fset.diff (A T) s _s2 <-> In a1 (map fst ss')).
  {
    intros a1; unfold s, _s2, ss', ss.
    rewrite  Fset.mem_diff, Bool.Bool.andb_true_iff, Fset.mem_union, Bool.Bool.orb_true_iff.
    unfold Fset.map.
    rewrite Bool.negb_true_iff, <- not_true_iff_false, !Fset.mem_mk_set, !Oset.mem_bool_true_iff.
    rewrite !map_map, map_app.
    split.
    - intros [[H1 | H1] H2].
      + apply in_or_app; left.
        rewrite in_map_iff in H1; destruct H1 as [b1 [H1 K1]].
        assert (J1 := Oset.in_permut_in _ K1 (Oset.permut_sym Hp1)).
        assert (K2 := apply_renaming_att_alt _ ss1 Hf1 b1 a1 J1 H1).
        rewrite in_map_iff; eexists; split; [ | apply K2]; apply refl_equal.
      + apply in_or_app; right.
        rewrite in_map_iff in H1; destruct H1 as [b1 [H1 K1]].
        assert (J1 := Oset.in_permut_in _ K1 (Oset.permut_sym Hp2)).
        assert (K2 := apply_renaming_att_alt _ ss2 Hf2 b1 a1 J1 H1).
        rewrite in_map_iff; exists (b1, a1); split; [apply refl_equal | ].
        rewrite filter_In; split; [assumption | simpl].
        rewrite Bool.negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff.
        intro L1; apply H2.
        rewrite in_map_iff; exists b1; split; [assumption | ].
        rewrite Fset.elements_inter; split; [ | assumption].
        apply (Oset.in_permut_in _ L1 Hp1).
    - intro H1; generalize (in_app_or _ _ _ H1); clear H1; intros [H1 | H1].
      + rewrite in_map_iff in H1.
        destruct H1 as [[b1 _a1] [_H1 H1]]; simpl in _H1; subst _a1.
        split.
        * left.
          rewrite in_map_iff; exists b1; split.
          -- apply apply_renaming_att; trivial.
          -- refine (Oset.in_permut_in _ _ Hp1).
             rewrite in_map_iff; eexists; split; [ | apply H1]; apply refl_equal.
        * intro H2; rewrite in_map_iff in H2.
          destruct H2 as [b2 [_H2 H2]].
          apply (Hs a1).
          -- rewrite in_map_iff; eexists; split; [ | apply H1]; apply refl_equal.
          -- rewrite in_map_iff; exists (b2, a1); split; [apply refl_equal | ].
             apply apply_renaming_att_alt; trivial.
             refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp2)).
             rewrite Fset.elements_inter in H2; apply (proj2 H2).
      + rewrite in_map_iff in H1.
        destruct H1 as [[b1 _a1] [_H1 H1]]; simpl in _H1; subst _a1.
        rewrite filter_In in H1; destruct H1 as [H1 K1].
        simpl in K1.
        rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff in K1.
        split.
        * right.
          rewrite in_map_iff; exists b1; split.
          -- apply apply_renaming_att; trivial.
          -- refine (Oset.in_permut_in _ _ Hp2).
             rewrite in_map_iff; eexists; split; [ | apply H1]; apply refl_equal.
        * intro H2; rewrite in_map_iff in H2.
          destruct H2 as [b2 [_H2 H2]].
          apply K1.
          rewrite <- (apply_renaming_att _ ss2 Hf2 _ _ H1) in _H2.
          assert (Abs : b2 = b1).
          {
            apply Hr2.
            - rewrite Fset.elements_inter in H2.
              apply (Fset.in_elements_mem _ _ _ (proj2 H2)).
            - apply Fset.in_elements_mem. 
              refine (Oset.in_permut_in _ _ Hp2).
              rewrite in_map_iff; eexists; split; [ | apply H1]; apply refl_equal.
            - apply _H2.
          }
          subst b2.
          refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp1)).
          rewrite Fset.elements_inter in H2; apply (proj1 H2).
  }
  apply eq_trans with
      (Oeset.nb_occ 
         (OTuple T) u
         (filter f_join 
                 (natural_join_list (map (rename_tuple _ rho1) l1) (map (rename_tuple _ rho2) l2)))).
  + rewrite Oeset.nb_occ_filter, Hfu;  [apply refl_equal | ].
    intros x1 x2 Hx1 Hx; unfold f_join.
    rewrite 2 Fset.for_all_spec; apply forallb_eq.
    intros a Ha.
    rewrite Oeset.mem_bool_true_iff in Hx1.
    destruct Hx1 as [y1 [Hx1 Hy1]].
    unfold natural_join_list in Hy1; rewrite in_theta_join_list in Hy1.
    destruct Hy1 as [z1 [z2 [Hz1 [Hz2 [Hj Hz]]]]].
    rewrite tuple_eq in Hx; rewrite 2 (proj2 Hx); trivial;
      rewrite tuple_eq in Hx1; rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)), Hz;
    unfold join_tuple; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
    * rewrite in_map_iff in Hz2.
      destruct Hz2 as [zz2 [Hzz2 Hz2]]; rewrite <- Hzz2, Bool.Bool.orb_true_iff; right.
      assert (Kzz2 : labels T zz2 =S= Fset.mk_set (A T) (map fst ss2)).
      {
        rewrite (Fset.equal_eq_1 _ _ _ _ (Hl2 _ Hz2)).
        rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.permut_elements_mk_set_alt _ _ Hp2)).
        apply Fset.equal_refl.
      }
      unfold rho2 at 2.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_rename_tuple_apply_renaming _ ss2 Hf2 Hs2 zz2 Kzz2)).
      assert (Ka := Fset.in_elements_mem _ _ _ Ha); 
        rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ka.
      assert (Ja := Oset.in_permut_in 
                      a (Fset.mem_in_elements _ _ _ (proj2 Ka)) (Oset.permut_sym Hp2)).
      rewrite in_map_iff in Ja.
      destruct Ja as [[_a b] [_Ja Ja]]; simpl in _Ja; subst _a.
      unfold rho2.
      rewrite (apply_renaming_att _ ss2 Hf2 _ _ Ja), Fset.mem_mk_set, Oset.mem_bool_true_iff.
      rewrite in_map_iff; eexists; split; [ | apply Ja]; apply refl_equal.
    * rewrite in_map_iff in Hz1.
      destruct Hz1 as [zz1 [Hzz1 Hz1]]; rewrite <- Hzz1, Bool.Bool.orb_true_iff; left.
      assert (Kzz1 : labels T zz1 =S= Fset.mk_set (A T) (map fst ss1)).
      {
        rewrite (Fset.equal_eq_1 _ _ _ _ (Hl1 _ Hz1)).
        rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.permut_elements_mk_set_alt _ _ Hp1)).
        apply Fset.equal_refl.
      }
      unfold rho1 at 2.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_rename_tuple_apply_renaming _ ss1 Hf1 Hs1 zz1 Kzz1)).
      assert (Ka := Fset.in_elements_mem _ _ _ Ha); 
        rewrite Fset.mem_inter, Bool.Bool.andb_true_iff in Ka.
      assert (Ja := Oset.in_permut_in 
                      a (Fset.mem_in_elements _ _ _ (proj1 Ka)) (Oset.permut_sym Hp1)).
      rewrite in_map_iff in Ja.
      destruct Ja as [[_a b] [_Ja Ja]]; simpl in _Ja; subst _a.
      unfold rho1.
      rewrite (apply_renaming_att _ ss1 Hf1 _ _ Ja), Fset.mem_mk_set, Oset.mem_bool_true_iff.
      rewrite in_map_iff; eexists; split; [ | apply Ja]; apply refl_equal.
  + set (l := filter f_join
          (natural_join_list (map (rename_tuple _ rho1) l1) (map (rename_tuple _ rho2) l2))).
    assert (Hl : forall x : tuple T, In x l -> labels T x =S= s).
    {
      intros x Hx; unfold l, natural_join_list in Hx.
      rewrite filter_In, in_theta_join_list in Hx.
      destruct Hx as [[x1 [x2 [Hx1 [Hx2 [Hx Kx]]]]] Jx]; rewrite Kx.
      unfold join_tuple, s; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
      apply Fset.union_eq.
      - rewrite in_map_iff in Hx1.
        destruct Hx1 as [y1 [_Hx1 Hy1]]; rewrite <- _Hx1.
        unfold rename_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
        unfold Fset.map.
        rewrite (Fset.elements_spec1 _ _ _ (Hl1 _ Hy1)).
        apply Fset.equal_refl.
      - rewrite in_map_iff in Hx2.
        destruct Hx2 as [y2 [_Hx2 Hy2]]; rewrite <- _Hx2.
        unfold rename_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
        unfold Fset.map.
        rewrite (Fset.elements_spec1 _ _ _ (Hl2 _ Hy2)).
        apply Fset.equal_refl.
    }
    set (tau := 
           fun a => apply_renaming
                      _ ss1 (apply_renaming _
                             (map (fun x => match x with (x1, x2) => (x2, x1) end) ss2) a)).
    assert (Htau : forall a b, In b ({{{s1 interS s2}}}) -> rho2 b = a -> tau a = rho1 b).
    {
      intros a b Hb H.
      unfold tau; fold rho1.
      apply f_equal.
      apply apply_renaming_att.
      - apply (all_diff_eq Hs2); rewrite map_map, <- map_eq.
        intros [] _; apply refl_equal.
      - rewrite in_map_iff; exists (b, a); split; [apply refl_equal | ].
        unfold rho2 in H.
        apply apply_renaming_att_alt; trivial.
          generalize (Fset.in_elements_mem _ _ _ Hb);
            rewrite Fset.mem_inter, Bool.Bool.andb_true_iff; intros [_ Jb].
          apply (Oset.in_permut_in
                   _ (Fset.mem_in_elements _ _ _ Jb) (Oset.permut_sym Hp2)).
      }
    assert (Hr : forall a : attribute T, a inS _s2 -> tau a inS Fset.diff (A T) s _s2).
    {
      intros a Ha.
      unfold _s2, Fset.map in Ha.
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha.
      destruct Ha as [b [_Ha Ha]].
      assert (Ka := Htau _ _ Ha _Ha).
      assert (Hb : rho1 b inS Fset.map (A T) (A T) rho1 s1).
      {
        unfold Fset.map; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
        exists b; split; [apply refl_equal | ].
        apply Fset.mem_in_elements.
        generalize (Fset.in_elements_mem _ _ _ Ha);
          rewrite Fset.mem_inter, Bool.Bool.andb_true_iff.
        apply proj1.
      }
      rewrite Ka, Fset.mem_diff, Bool.Bool.andb_true_iff; split.
      - unfold s; rewrite Fset.mem_union, Bool.Bool.orb_true_iff; left; apply Hb.
      - case_eq (rho1 b inS? _s2); intro Kb; [ | apply refl_equal].
        unfold _s2 in Kb.
        rewrite Fset.equal_spec in Hd; assert (Hda := Hd (rho1 b)).
        rewrite Fset.empty_spec, Fset.mem_inter, Hb in Hda.
        assert (Abs : (rho1 b inS Fset.map (A T) (A T) rho2 s2)).
        {
          revert Kb; unfold Fset.map; 
            rewrite 2 Fset.mem_mk_set, 2 Oset.mem_bool_true_iff, 2 in_map_iff.
          intros [c [Hc Kc]]; exists c; split; [assumption | ].
          apply Fset.mem_in_elements.
          generalize (Fset.in_elements_mem _ _ _ Kc); 
            rewrite Fset.mem_inter, Bool.Bool.andb_true_iff.
          apply proj2.
        }
        rewrite Abs in Hda; discriminate Hda.
    }
    assert (Hr' : forall x, In x l -> forall a, a inS _s2 -> dot T x a = dot T x (tau a)).
    {
      intros x Hx a Ha.
      unfold _s2, Fset.map in Ha.
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha.
      destruct Ha as [b [_Ha Ha]]; rewrite <- _Ha at 1; fold rho2.
      assert (Ka := Htau _ _ Ha _Ha).
      apply sym_eq; rewrite Ka, <- (Oset.eq_bool_true_iff (OVal T)).
      unfold l in Hx; rewrite filter_In in Hx.
      destruct Hx as [Hx Hfx].
      unfold f_join in Hfx.
      rewrite Fset.for_all_spec, forallb_forall in Hfx.
      apply Hfx; assumption.
    }
    assert (Hr'' : forall a : attribute T, a inS _s2 -> dot T u a = dot T u (tau a)).
    {
      intros a Ha.
      unfold _s2, Fset.map in Ha.
      rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha.
      destruct Ha as [b [_Ha Ha]]; rewrite <- _Ha at 1; fold rho2.
      assert (Ka := Htau _ _ Ha _Ha).
      apply sym_eq; rewrite Ka, <- (Oset.eq_bool_true_iff (OVal T)).
      unfold f_join in Hfu.
      rewrite Fset.for_all_spec, forallb_forall in Hfu.
      apply Hfu; assumption.
    }
    rewrite <- (remove_dup_cols l tau s _s2 _Hs2 Hr Hl Hr' u Ku Hr'').
    rewrite <- (nb_occ_map_rename_tuple _ rho'), map_map.
    assert (HH1 :
              forall x, 
                labels T x =S= s ->
                labels T (rename_tuple _ rho' (mk_tuple T (Fset.diff (A T) s _s2) (dot T x))) =S=
                labels T (mk_tuple T (s1 unionS s2) (fun a : attribute T => dot T x (rho a)))).
    {
      intros x Hx.
      rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 (rename_tuple_ok _ _ _))).
      unfold Fset.map.
      rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)).
      rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
      rewrite Fset.equal_spec; intro a.
      rewrite Fset.mem_mk_set, eq_bool_iff, Oset.mem_bool_true_iff, in_map_iff; split.
      + intros [b [Hb Kb]].
        assert (Jb := Fset.in_elements_mem _ _ _ Kb).
        rewrite Aux in Jb.
        rewrite <- Hss' in Hs'.
        assert (Lb := apply_renaming_att_alt _ ss' Hs' b a Jb Hb).
        unfold ss' in Lb; rewrite in_map_iff in Lb.
        destruct Lb as [[_a _b] [_Lb Lb]]; injection _Lb; clear _Lb; do 2 intro; subst _a _b.
        unfold ss in Lb.
        destruct (in_app_or _ _ _ Lb) as [Mb | Mb].
        * rewrite Fset.mem_union, Bool.Bool.orb_true_iff.
          left; apply Fset.in_elements_mem.
          refine (Oset.in_permut_in _ _ Hp1).
          rewrite in_map_iff; eexists; split; [ | apply Mb]; apply refl_equal.
        * rewrite Fset.mem_union, Bool.Bool.orb_true_iff.
          right; apply Fset.in_elements_mem.
          refine (Oset.in_permut_in _ _ Hp2).
          rewrite filter_In in Mb.
          rewrite in_map_iff; eexists; split; [ | apply (proj1 Mb)]; apply refl_equal.
      + intro H1.
        case_eq (a inS? s1); intro H1'.
        * assert (K1 := 
                    Oset.in_permut_in _ (Fset.mem_in_elements _ _ _ H1') (Oset.permut_sym Hp1)).
          rewrite in_map_iff in K1.
          destruct K1 as [[_a b] [_K1 K1]]; simpl in _K1; subst _a.
          exists b; split.
          -- apply (apply_renaming_att _ ss').
             ++ rewrite <- Hss' in Hs'; assumption.
             ++ unfold ss', ss.
                rewrite map_app; apply in_or_app; left.
                rewrite in_map_iff; eexists; split; [ | apply K1]; apply refl_equal.
          -- apply Fset.mem_in_elements.
             rewrite Aux; unfold ss'; rewrite map_map, in_map_iff.
             exists (a, b); split; [apply refl_equal | ].
             unfold ss; apply in_or_app; left; assumption.
        * rewrite Fset.mem_union, H1' in H1; simpl in H1.
          assert (K1 := 
                    Oset.in_permut_in _ (Fset.mem_in_elements _ _ _ H1) (Oset.permut_sym Hp2)).
          rewrite in_map_iff in K1.
          destruct K1 as [[_a b] [_K1 K1]]; simpl in _K1; subst _a.
          exists b; split.
          -- apply (apply_renaming_att _ ss').
             ++ rewrite <- Hss' in Hs'; assumption.
             ++ unfold ss', ss.
                rewrite map_app; apply in_or_app; right.
                rewrite in_map_iff; exists (a, b); split; [apply refl_equal | ].
                rewrite filter_In; split; [assumption | simpl].
                rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff, in_map_iff.
                intros [[_a b1] [_J1 J1]]; simpl in _J1; subst _a.
                rewrite <- not_true_iff_false in H1'.
                apply H1'.
                apply Fset.in_elements_mem.
                refine (Oset.in_permut_in _ _ Hp1).
                rewrite in_map_iff; eexists; split; [ | apply J1]; apply refl_equal.
          -- apply Fset.mem_in_elements.
             rewrite Aux; unfold ss'; rewrite map_map, in_map_iff.
             exists (a, b); split; [apply refl_equal | ].
             unfold ss; apply in_or_app; right.
             rewrite filter_In; split; [assumption | simpl].
             rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff, in_map_iff.
             intros [[_a b1] [_J1 J1]]; simpl in _J1; subst _a.
             rewrite <- not_true_iff_false in H1'.
             apply H1'.
             apply Fset.in_elements_mem.
             refine (Oset.in_permut_in _ _ Hp1).
             rewrite in_map_iff; eexists; split; [ | apply J1]; apply refl_equal.
    }
    assert (HH2 : forall x, 
               labels T x =S= s ->
               rename_tuple _ rho' (mk_tuple T (Fset.diff (A T) s _s2) (dot T x)) =t=
               mk_tuple T (s1 unionS s2) (fun a : attribute T => dot T x (rho a))).
    {
      intros x Hx; rewrite tuple_eq; split; [apply HH1; assumption | ].
      intros a Ha; assert (_Ha := Ha).
      rewrite (Fset.mem_eq_2 _ _ _ (HH1 _ Hx)), 
         (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in _Ha.
      rewrite dot_mk_tuple, _Ha.
      rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ _ _))) in Ha.
      unfold Fset.map in Ha; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ha.
      destruct Ha as [b [__Ha Ha]]; rewrite <- __Ha at 1.
      rewrite (proj2 (rename_tuple_ok _ rho' ( (mk_tuple T (Fset.diff (A T) s _s2) (dot T x))))).
      - rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
        rewrite dot_mk_tuple, (Fset.in_elements_mem _ _ _ Ha).
        apply f_equal.
        apply sym_eq.
        apply apply_renaming_att; trivial.
        rewrite <- Hss' in Hs'.
        generalize (Fset.in_elements_mem _ _ _ Ha); rewrite Aux; clear Ha; intro Ha.
        assert (Aux2 := apply_renaming_att_alt _ ss' Hs' b a Ha __Ha).
        unfold ss' in Aux2.
        rewrite in_map_iff in Aux2.
        destruct Aux2 as [[_a _b] [_Aux2 Aux2]]; injection _Aux2; clear _Aux2; do 2 intro.
        subst _a _b; assumption.
      - intros a1 a2 Ha1 Ha2; apply all_diff_one_to_one_apply_renaming.
        + rewrite Hss'; assumption.
        + rewrite <- Hss; assumption.
        + rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Aux in Ha1; assumption.
        + rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Aux in Ha2; assumption.
      - apply Fset.in_elements_mem; assumption.
    }
    rewrite (Oeset.nb_occ_eq_1 _ _ _ _ (HH2 u Ku)).
    assert (Ju : (mk_tuple T (s1 unionS s2) (fun a : attribute T => dot T u (rho a))) =t= t).
    {
      rewrite tuple_eq; split;
        [rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _));
         rewrite (Fset.equal_eq_2 _ _ _ _ Ht); apply Fset.equal_refl | ].
      intros a Ha; rewrite dot_mk_tuple.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha; rewrite Ha.
      unfold u; unfold join_tuple.
      rewrite dot_mk_tuple.
      case_eq (a inS? s1); intro Ha1.
      - assert (Hra : rho a = rho1 a).
        {
          assert (Ka1 : In a (map fst ss1)).
          {
            refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp1)).
            apply Fset.mem_in_elements; assumption.
          }
          rewrite in_map_iff in Ka1; destruct Ka1 as [[_a1 b1] [_Ka1 Ka1]].
          simpl in _Ka1; subst _a1.
          unfold rho1; rewrite (apply_renaming_att _ ss1) with a b1; trivial.
          unfold rho; apply apply_renaming_att; trivial.
          unfold ss; apply in_or_app; left; assumption.
        }
        assert (Ka1 : rho a inS labels T u1).
        {
          unfold u1 at 1.
          rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ _ _))).
          unfold Fset.map, t1 at 1.
          rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_mk_set.
          rewrite Oset.mem_bool_true_iff, in_map_iff.
          exists a; split; [apply sym_eq | apply Fset.mem_in_elements]; assumption.
        }
        rewrite Fset.mem_union, Ka1, Hra; simpl.
        unfold u1.
        rewrite (proj2 (rename_tuple_ok _ _ _)).
        + unfold t1; rewrite dot_mk_tuple, Ha1; apply refl_equal.
        + intros a1 a2 _Ha1 Ha2; apply Hr1.
          * unfold t1 in _Ha1; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in _Ha1.
            assumption.
          * unfold t1 in Ha2; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha2.
            assumption.
        + unfold t1; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); assumption.
      - rewrite Fset.mem_union, Ha1 in Ha; simpl in Ha.
        assert (Hra : rho a = rho2 a).
        {
          assert (Ka1 : In a (map fst ss2)).
          {
            refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp2)).
            apply Fset.mem_in_elements; assumption.
          }
          rewrite in_map_iff in Ka1; destruct Ka1 as [[_a1 b1] [_Ka1 Ka1]].
          simpl in _Ka1; subst _a1.
          unfold rho2; rewrite (apply_renaming_att _ ss2) with a b1; trivial.
          unfold rho; apply apply_renaming_att; trivial.
          unfold ss; apply in_or_app; right.
          rewrite filter_In; split; [assumption | ].
          rewrite negb_true_iff, <- not_true_iff_false, Oset.mem_bool_true_iff, in_map_iff.
          intros [[_a b2] [_H H]]; simpl in _H; subst _a.
          rewrite <- not_true_iff_false in Ha1; apply Ha1.
          apply Fset.in_elements_mem.
          refine (Oset.in_permut_in _ _ Hp1).
          rewrite in_map_iff; eexists; split; [ | apply H]; apply refl_equal.
        }
        assert (Ka1 : rho a inS labels T u2).
        {
          unfold u2 at 1.
          rewrite (Fset.mem_eq_2 _ _ _ (proj1 (rename_tuple_ok _ _ _))).
          unfold Fset.map, t2 at 1.
          rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_mk_set.
          rewrite Oset.mem_bool_true_iff, in_map_iff.
          exists a; split; [apply sym_eq | apply Fset.mem_in_elements]; assumption.
        }
        rewrite Fset.mem_union, Ka1, Bool.Bool.orb_true_r, Hra; simpl.
        assert (Ja1 : rho2 a inS? labels T u1 = false).
        {
          rewrite <- not_true_iff_false; intro Ja1.
          unfold u1, rename_tuple in Ja1.
          rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ja1.
          unfold Fset.map in Ja1.
          rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Ja1.
          destruct Ja1 as [a' [_Ja1 Ja1]].
          unfold t1 in Ja1; rewrite (Fset.elements_spec1 _ _ _ (labels_mk_tuple _ _ _)) in Ja1.
          apply (Hs (rho2 a)).
          - rewrite <- _Ja1, in_map_iff.
            exists (a', rho1 a'); split; [apply refl_equal | ].
            apply apply_renaming_att_alt; trivial.
            refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp1)); assumption.
          - rewrite in_map_iff; exists (a, rho2 a); split; [apply refl_equal | ].
            apply apply_renaming_att_alt; trivial.
            refine (Oset.in_permut_in _ _ (Oset.permut_sym Hp2)); 
              apply Fset.mem_in_elements; assumption.
        }
        rewrite Ja1.
        unfold u2.
        rewrite (proj2 (rename_tuple_ok _ _ _)).
        + unfold t2; rewrite dot_mk_tuple, Ha; apply refl_equal.
        + intros a1 a2 _Ha1 Ha2; apply Hr2.
          * unfold t2 in _Ha1; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in _Ha1.
            assumption.
          * unfold t2 in Ha2; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha2.
            assumption.
        + unfold t2; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); assumption.
    }
    rewrite (Oeset.nb_occ_eq_1 _ _ _ _ Ju).
    apply (Oeset.nb_occ_map_eq_2_alt (OTuple T)).
    * intros x Hx; apply HH2.
      apply Hl; assumption.
    * intros a1 a2 x Hx Ha1 Ha2.
      apply all_diff_one_to_one_apply_renaming.
      -- rewrite <- Hss' in Hs'; assumption.
      -- rewrite Hss in Hf; assumption.
      -- rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Aux in Ha1.
         assumption.
      -- rewrite Oeset.mem_bool_true_iff in Hx.
         destruct Hx as [x' [Hx Hx']].
         rewrite tuple_eq in Hx; rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx)) in Ha2.
         rewrite in_map_iff in Hx'.
         destruct Hx' as [x'' [Hx' Hx'']]; subst x'.
         rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Aux in Ha2.
         assumption.
- case_eq (Oeset.nb_occ (OTuple T) t
    (map (fun x : tuple T => mk_tuple T (s1 unionS s2) (fun a : attribute T => dot T x (rho a)))
       (filter f_join
          (natural_join_list (map (rename_tuple _ rho1) l1) (map (rename_tuple _ rho2) l2)))));
    [intros; apply refl_equal | ].
  intros p Hp.
  assert (Aux : Oeset.mem_bool (OTuple T) t
         (map
            (fun x : tuple T =>
             mk_tuple T (s1 unionS s2) (fun a : attribute T => dot T x (rho a)))
            (filter f_join
               (natural_join_list (map (rename_tuple _ rho1) l1) (map (rename_tuple _ rho2) l2)))) = 
                true).
  {
    apply Oeset.nb_occ_mem.
    rewrite Hp; discriminate.
  }
  rewrite Oeset.mem_bool_true_iff in Aux.
  destruct Aux as [t' [Ht' Kt']].
  rewrite in_map_iff in Kt'.
  destruct Kt' as [t'' [Kt' Kt'']].
  rewrite tuple_eq in Ht'.
  rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 Ht')) in Ht.
  rewrite <- Kt', (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)) in Ht.
  rewrite Fset.equal_refl in Ht.
  discriminate Ht.
Qed.

End Sec.
