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

Require Import List NArith.
Require Import BasicFacts ListFacts ListPermut OrderedSet.

Section Sec.

Hypothesis data : Type.
Hypothesis OD : Oeset.Rcd data.

Notation "x1 '=d=' x2" := (Oeset.compare OD x1 x2 = Eq) (at level 70, no associativity).
Notation "s1 '=PE=' s2" := (Oeset.permut OD s1 s2) (at level 70, no associativity).

Hypothesis join : data -> data -> data.
Hypothesis join_eq_1 : forall x1 x2 x, x1 =d= x2 -> join x1 x =d= join x2 x.
Hypothesis join_eq_2 : forall x x1 x2, x1 =d= x2 -> join x x1 =d= join x x2.

Definition d_join_list (f : data -> data -> bool) x l := map (join x) (filter (f x) l).

Definition theta_join_list f l1 l2 := flat_map (fun x1 => d_join_list f x1 l2) l1.

Lemma d_join_list_unfold :
  forall f x l, d_join_list f x l =  map (join x) (filter (f x) l).
Proof.
intros; apply refl_equal.
Qed.

Lemma theta_join_list_unfold : 
  forall f l1 l2, theta_join_list f l1 l2 = flat_map (fun x1 => d_join_list f x1 l2) l1.
Proof.
intros; apply refl_equal.
Qed.

Lemma d_join_list_cons :
  forall f x x1 l, 
    d_join_list f x (x1 :: l) = 
    if f x x1 then join x x1 :: d_join_list f x l else d_join_list f x l.
Proof.
intros f x x1 l; rewrite d_join_list_unfold; simpl.
case (f x x1); simpl; apply refl_equal.
Qed.

Lemma d_join_list_eq_1 :
  forall f f' x l2, 
    (forall t2, In t2 l2 -> f x t2 = f' x t2) -> d_join_list f x l2 = d_join_list f' x l2.
Proof.
intros f f' x l2;
  induction l2 as [ | x2 l2]; intro H; [apply refl_equal | ].
rewrite 2 d_join_list_cons.
rewrite <- (H x2 (or_introl _ (refl_equal _))).
rewrite <- IHl2; trivial.
intros; apply H; right; assumption.
Qed.

Lemma theta_join_list_eq_1 :
  forall f f' l1 l2,
    (forall t1 t2, In t1 l1 -> In t2 l2 -> f t1 t2 = f' t1 t2) ->
    theta_join_list f l1 l2 = theta_join_list f' l1 l2.
Proof.
intros f f' l1; induction l1 as [ | x1 l1]; intros l2 H; simpl; [apply refl_equal | ].
apply f_equal2.
- apply d_join_list_eq_1.
  intro; apply H; left; apply refl_equal.
- apply IHl1.
  do 3 intro; apply H; right; assumption.
Qed.

Lemma d_join_list_app :
  forall f x l l', d_join_list f x (l ++ l') = d_join_list f x l ++ d_join_list f x l'.
Proof.
unfold d_join_list.
intros f x l; induction l as [ | x1 l]; intro l'; simpl; [apply refl_equal | ].
case (f x x1); simpl; rewrite IHl; trivial.
Qed.

Lemma theta_join_list_app_1 :
  forall f l1 l2 l, 
    theta_join_list f (l1 ++ l2) l = theta_join_list f l1 l ++ theta_join_list f l2 l.
Proof.
intros f l1 l2 l; unfold theta_join_list.
rewrite flat_map_app; apply refl_equal.
Qed.

Lemma theta_join_list_app_2 :
  forall f l1 l2 l, 
    _permut eq (theta_join_list f l (l1 ++ l2)) (theta_join_list f l l1 ++ theta_join_list f l l2).
Proof.
intros f l1 l2 l; unfold theta_join_list.
revert l1 l2; induction l as [ | t l]; intros l1 l2; simpl; [apply Pnil | ].
rewrite d_join_list_app, <- 2 ass_app.
apply _permut_app1; [apply equivalence_eq | ].
assert (IH := IHl l1 l2).
rewrite (_permut_app1 (equivalence_eq _) (d_join_list f t l2)) in IH.
refine (_permut_trans _ IH _); [intros; subst; apply refl_equal | ].
rewrite 2 ass_app; apply _permut_app2; [apply equivalence_eq | ].
apply _permut_swapp; apply _permut_refl; intros; trivial.
Qed.

Lemma in_d_join_list :  
  forall f x1 l2 x,
    In x (d_join_list f x1 l2) <-> (exists x2, In x2 l2 /\ f x1 x2 = true /\ x = join x1 x2).
Proof.
intros f x1 s2 t; unfold d_join_list.
rewrite in_map_iff; split.
- intros [x2 [Hx2 Hx]].
  rewrite filter_In in Hx.
  exists x2; split; [apply (proj1 Hx) | ].
  split; [apply (proj2 Hx) | ].
  apply sym_eq; assumption.
- intros [x2 [Hx2 Hx]].
  exists x2; split; [apply sym_eq; apply (proj2 Hx) | ].
  rewrite filter_In.
  split; [apply Hx2 | apply (proj1 Hx)].
Qed.

Lemma in_theta_join_list :  
  forall f l1 l2 x,
    In x (theta_join_list f l1 l2) <->
    (exists x1 x2, In x1 l1 /\ In x2 l2 /\ f x1 x2 = true /\ x = join x1 x2).
Proof.
intros f s1 s2 t; unfold theta_join_list, d_join_list.
rewrite in_flat_map; split.
- intros [x1 [Hx1 Ht]].
  rewrite (in_d_join_list f x1 s2 t) in Ht; destruct Ht as [x2 Ht].
  exists x1; exists x2; split; assumption.
- intros [x1 [x2 [Hx2 H]]].
  exists x1; split; [assumption | ].
  rewrite (in_d_join_list f x1 s2 t); exists x2; assumption.
Qed.

Lemma d_join_list_mem_bool_impl :
  forall f, (forall x x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
    forall x l1 l2, 
      (forall t, Oeset.mem_bool OD t l1 = true -> Oeset.mem_bool OD t l2 = true) -> 
      forall t, Oeset.mem_bool OD t (d_join_list f x l1) = true ->
                Oeset.mem_bool OD t (d_join_list f x l2) = true.
Proof.
intros f Hf x l1 l2 H t Ht.
rewrite Oeset.mem_bool_true_iff in Ht.
destruct Ht as [t' [Ht Ht']].
rewrite in_d_join_list in Ht'.
destruct Ht' as [x2 [Hx2 [Hx H']]]; subst t'.
assert (Hx2' : Oeset.mem_bool OD x2 l2 = true).
{
  apply H; rewrite Oeset.mem_bool_true_iff.
  exists x2; split; [ | assumption].
  apply Oeset.compare_eq_refl.
}
rewrite Oeset.mem_bool_true_iff in Hx2'.
destruct Hx2' as [x2' [Hx2' H']].
rewrite Oeset.mem_bool_true_iff.
exists (join x x2'); split.
- refine (Oeset.compare_eq_trans _ _ _ _ Ht _).
  apply join_eq_2; assumption.
- rewrite in_d_join_list.
  exists x2'; split; [assumption | split; [ | apply refl_equal]].
  rewrite <- Hx; apply sym_eq; apply Hf; assumption.
Qed.  

Lemma d_join_list_mem_bool_eq_2 :
  forall f, (forall x x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
  forall x l1 l2, 
    (forall t, Oeset.mem_bool OD t l1 = Oeset.mem_bool OD t l2) -> 
    forall t, Oeset.mem_bool OD t (d_join_list f x l1) = Oeset.mem_bool OD t (d_join_list f x l2).
Proof.
intros f Hf x l1 l2 H t.
apply eq_bool_iff; split; apply d_join_list_mem_bool_impl; trivial.
- intro; rewrite H; exact (fun h => h).
- intro; rewrite H; exact (fun h => h).
Qed.

Lemma theta_join_list_mem_bool_impl_2 :
  forall f, (forall x x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
  forall l l1 l2, 
    (forall t, Oeset.mem_bool OD t l1 = true -> Oeset.mem_bool OD t l2 = true) -> 
    forall t, Oeset.mem_bool OD t (theta_join_list f l l1) = true ->
              Oeset.mem_bool OD t (theta_join_list f l l2) = true.
Proof.
intros f Hf l; induction l as [ | x l]; intros l1 l2 Hl t; simpl; [exact (fun h => h) | ].
rewrite 2 Oeset.mem_bool_app, 2 Bool.orb_true_iff.
intros [H | H]; [left | right; apply IHl with l1; trivial].
revert H; apply d_join_list_mem_bool_impl; trivial.
Qed.

Lemma theta_join_list_mem_bool_eq_2 :
  forall f, (forall x x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
  forall l l1 l2, 
    (forall t, Oeset.mem_bool OD t l1 = Oeset.mem_bool OD t l2) -> 
    forall t, Oeset.mem_bool OD t (theta_join_list f l l1) = 
              Oeset.mem_bool OD t (theta_join_list f l l2).
Proof.
intros f Hf l l1 l2 H t.
apply eq_bool_iff; split; apply theta_join_list_mem_bool_impl_2; trivial.
- intro; rewrite H; exact (fun h => h).
- intro; rewrite H; exact (fun h => h).
Qed.

Lemma theta_join_list_mem_bool_impl_1 :
  forall f, (forall x1 x2 x, x1 =d= x2 -> f x1 x = f x2 x) -> 
  forall l1 l2 l, 
    (forall t, Oeset.mem_bool OD t l1 = true -> Oeset.mem_bool OD t l2 = true) -> 
    forall t, Oeset.mem_bool OD t (theta_join_list f l1 l) = true ->
              Oeset.mem_bool OD t (theta_join_list f l2 l) = true.
Proof.
intros f Hf l1 l2 l Hl u Hu.
rewrite Oeset.mem_bool_true_iff in Hu.
destruct Hu as [u' [Hu Hu']]; rewrite in_theta_join_list in Hu'.
destruct Hu' as [t1 [t [Ht1 [Ht [H H']]]]]; subst u'.
assert (Kt1 : Oeset.mem_bool OD t1 l2 = true).
{
  apply Hl; rewrite Oeset.mem_bool_true_iff.
  exists t1; split; [apply Oeset.compare_eq_refl | assumption].
}
rewrite Oeset.mem_bool_true_iff in Kt1; destruct Kt1 as [t2 [Kt1 Ht2]].
rewrite Oeset.mem_bool_true_iff.
exists (join t2 t); split.
- refine (Oeset.compare_eq_trans _ _ _ _ Hu _).
  apply join_eq_1; assumption.
- rewrite in_theta_join_list.
  exists t2; exists t; repeat split; trivial.
  rewrite <- H; apply sym_eq; apply Hf; assumption.
Qed.

Lemma theta_join_list_mem_bool_eq_1 :
  forall f, (forall x1 x2 x, x1 =d= x2 -> f x1 x = f x2 x) -> 
  forall l1 l2 l, 
    (forall t, Oeset.mem_bool OD t l1 = Oeset.mem_bool OD t l2) -> 
    forall t, Oeset.mem_bool OD t (theta_join_list f l1 l) = 
              Oeset.mem_bool OD t (theta_join_list f l2 l).
Proof.
intros f Hf l1 l2 l H t.
apply eq_bool_iff; split; apply theta_join_list_mem_bool_impl_1; trivial.
- intro; rewrite H; exact (fun h => h).
- intro; rewrite H; exact (fun h => h).
Qed.

Lemma d_join_list_permut_eq_2 :
  forall f x l1 l2, 
    (forall x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
    l1 =PE= l2 -> d_join_list f x l1 =PE= d_join_list f x l2.
Proof.
intros f x l1; induction l1 as [ | x1 l1]; intros l2 Hf H.
- inversion H; subst; apply Oeset.permut_refl.
- inversion H; clear H; subst.
  rewrite d_join_list_app, 2 (d_join_list_unfold _ _ (_ :: _)); simpl.
  rewrite <- (Hf _ _ H2).
  case (f x x1); simpl.
  + apply Pcons; [apply join_eq_2; assumption | ].
    rewrite <- 2 d_join_list_unfold, <- d_join_list_app.
    apply IHl1; assumption.
  + rewrite <- 2 d_join_list_unfold, <- d_join_list_app; apply IHl1; assumption.
Qed.

Lemma theta_join_list_permut_eq_2 :
  forall f, (forall x x1 x2, x1 =d= x2 -> f x x1 = f x x2) -> 
    forall l l1 l2, l1 =PE= l2 -> theta_join_list f l l1 =PE= theta_join_list f l l2.
Proof.
intros f Hf l; induction l as [ | x l]; intros l1 l2 H; simpl.
- apply Oeset.permut_refl.
- apply _permut_app; [ | apply IHl; assumption].
  apply d_join_list_permut_eq_2.
  + do 2 intro; apply Hf.
  + assumption.
Qed.

Lemma theta_join_list_permut_eq_1 :
  forall f, (forall x1 x2 x, x1 =d= x2 -> f x1 x = f x2 x) -> 
    forall l1 l2 l, l1 =PE= l2 -> theta_join_list f l1 l =PE= theta_join_list f l2 l.
Proof.
intros f Hf l1 l2 l H1; rewrite 2 theta_join_list_unfold.
revert l l2 H1; induction l1 as [ | x1 l1]; intros l l2 H1.
- inversion H1; subst; apply Oeset.permut_refl.
- inversion H1; subst.
  rewrite flat_map_app; simpl.
  assert (IH := IHl1 l _ H4).
  rewrite (Oeset.permut_app1 _ (map (join x1) (filter (f x1) l))) in IH.
  apply (Oeset.permut_trans IH).
  rewrite flat_map_app, 2 ass_app.
  rewrite <- Oeset.permut_app2.
  apply _permut_swapp; [ | apply Oeset.permut_refl].
  clear l1 l3 H4 IHl1 H1 IH.
  induction l as [ | x l]; [apply Oeset.permut_refl | simpl].
  rewrite d_join_list_unfold; simpl.
  rewrite (Hf _ _ _ H2).
  case (f b x); [ | apply IHl].
  simpl; apply Oeset.permut_cons; [ | apply IHl].
  apply join_eq_1; assumption.
Qed.

Lemma theta_join_list_permut_eq :
  forall f, (forall x1 x2 x1' x2', x1 =d= x1' -> x2 =d= x2' -> f x1 x2 = f x1' x2') -> 
    forall l1 l1' l2 l2', 
      l1 =PE= l1' -> l2 =PE= l2' -> theta_join_list f l1 l2 =PE= theta_join_list f l1' l2'.
Proof.
intros f Hf l1 l1' l2 l2' H1 H2.
apply Oeset.permut_trans with (theta_join_list f l1 l2').
- apply theta_join_list_permut_eq_2; [ | assumption].
  intros; apply Hf; [apply Oeset.compare_eq_refl | assumption].
- apply theta_join_list_permut_eq_1; [ | assumption].
  intros; apply Hf; [assumption | apply Oeset.compare_eq_refl].
Qed.

Lemma theta_join_list_comm :
  forall f, 
    (forall x1 x2, f x1 x2 = f x2 x1) -> 
    (forall x1 x2, f x1 x2 = true -> join x1 x2 =d= join x2 x1) ->
    forall l1 l2, theta_join_list f l1 l2 =PE= theta_join_list f l2 l1.
Proof.
intros f Hf Hj l1 l2; apply Oeset.nb_occ_permut; intro t.
unfold theta_join_list.
revert l2; induction l1 as [ | t1 l1]; [intro l2; induction l2; simpl; trivial | ].
intro l2; rewrite flat_map_unfold, Oeset.nb_occ_app, IHl1.
clear IHl1; revert t1 l1; induction l2 as [ | t2 l2]; intros t1 l1; [apply refl_equal | ].
rewrite d_join_list_cons, 2 flat_map_unfold, 2 Oeset.nb_occ_app, <- IHl2, 
  d_join_list_cons, (Hf t2 t1).
rewrite !N.add_assoc; apply f_equal2; [ | apply refl_equal].
case_eq (f t1 t2); intro Hf12; [ | apply N.add_comm].
rewrite 2 (Oeset.nb_occ_unfold _ _ (_ :: _)), <- !N.add_assoc; apply f_equal2;
    [ | apply N.add_comm].
rewrite (Oeset.compare_eq_2 _ _ _ _ (Hj _ _ Hf12)); apply refl_equal.
Qed.

Lemma theta_join_list_assoc :
  forall f, 
    (forall x1 x2 x3, f x1 x2 = true -> f x2 x3 = true -> f (join x1 x2) x3 = f x1 (join x2 x3)) ->
    (forall x1 x2 x3, f x1 x2 = true -> f x2 x3 = false -> f (join x1 x2) x3 = false) ->
    (forall x1 x2 x3, f x1 x2 = false -> f x1 (join x2 x3) = false) ->
    (forall x1 x2 x3, join (join x1 x2) x3 =d= join x1 (join x2 x3)) ->
    forall l1 l2 l3, 
      theta_join_list f (theta_join_list f l1 l2) l3 =PE= 
      theta_join_list f l1 (theta_join_list f l2 l3).
Proof.
intros f Hf1 Hf2 Hf3 Hj l1 l2 l3; apply Oeset.nb_occ_permut; intro t.
unfold theta_join_list.
revert l2 l3; induction l1 as [ | t1 l1]; intros l2 l3; [apply refl_equal | ].
rewrite !flat_map_unfold, !flat_map_app, !Oeset.nb_occ_app.
apply f_equal2; [ | apply IHl1].
clear l1 IHl1.
revert l3; induction l2 as [ | t2 l2]; intro l3; [apply refl_equal | ].
rewrite !d_join_list_cons, flat_map_unfold, d_join_list_app, Oeset.nb_occ_app.
case_eq (f t1 t2); intro Hf12.
- rewrite flat_map_unfold, Oeset.nb_occ_app.
  apply f_equal2; [ | apply IHl2].
  clear l2 IHl2; induction l3 as [ | t3 l3]; [apply refl_equal | ].
  rewrite !d_join_list_cons.
  case_eq (f t2 t3); intro Hf23.
  + rewrite d_join_list_cons, (Hf1 _ _ _ Hf12 Hf23).
    case (f t1 (join t2 t3)); [ | apply IHl3].
    rewrite !(Oeset.nb_occ_unfold _ _ (_ :: _)).
    apply f_equal2; [ | apply IHl3].
    rewrite (Oeset.compare_eq_2 _ _ _ _ (Hj _ _ _)); apply refl_equal.
  + rewrite (Hf2 _ _ _ Hf12 Hf23); apply IHl3.
- rewrite <- N.add_0_l at 1; apply f_equal2; [ | apply IHl2].
  clear l2 IHl2; induction l3 as [ | t3 l3]; [apply refl_equal | ].
  rewrite d_join_list_cons.
  case (f t2 t3); [ | apply IHl3].
  rewrite d_join_list_cons, (Hf3 _ _ _ Hf12); apply IHl3.
Qed.

Definition brute_left_join_list s1 s2 := theta_join_list (fun _ _ => true) s1 s2.


Fixpoint N_join_list empty_d ll :=
  match ll with
    | nil => empty_d :: nil
    | s1 :: ll => brute_left_join_list s1 (N_join_list empty_d ll)
  end.

Lemma brute_left_join_list_unfold :
  forall s1 s2, brute_left_join_list s1 s2 = theta_join_list (fun _ _ => true) s1 s2.
Proof.
intros s1 s2; apply refl_equal.
Qed.

Lemma N_join_list_unfold :
  forall e ll, N_join_list e ll = 
               match ll with 
               | nil => e :: nil 
               | s1 :: ll => brute_left_join_list s1 (N_join_list e ll)
               end.
Proof.
intros e ll; case ll; intros; apply refl_equal.
Qed.

Lemma N_join_list_map_eq :
  forall (B : Type) e (l : list B) (f1 f2 : B -> list data),
  (forall x, In x l -> comparelA (Oeset.compare OD) (f1 x) (f2 x) = Eq) ->
  comparelA (Oeset.compare OD) (N_join_list e (map f1 l)) (N_join_list e (map f2 l)) = Eq.
Proof.
intros B e l; induction l as [ | a1 l]; intros f1 f2 Hf; simpl.
- rewrite Oeset.compare_eq_refl; trivial.
- unfold brute_left_join_list, theta_join_list.
  assert (H1 := Hf _ (or_introl _ (refl_equal _))).
  set (b1 := f1 a1) in *; clearbody b1.
  set (b2 := f2 a1) in *; clearbody b2.
  assert (IH := IHl f1 f2 (fun x h => Hf x (or_intror _ h))).
  set (l1 := N_join_list e (map f1 l)) in *; clearbody l1.
  set (l2 := N_join_list e (map f2 l)) in *; clearbody l2.
  revert b2 H1 l1 l2 IH; 
    induction b1 as [ | x1 b1]; 
    intros [ | x2 b2] H1 l1 l2 IH; simpl; trivial; try discriminate H1.
  simpl in H1.
  case_eq (Oeset.compare OD x1 x2); intro Ht;
  rewrite Ht in H1; try discriminate H1.
  apply comparelA_eq_app; [ | apply IHb1; trivial].
  clear b1 b2 IHb1 H1.
  revert x1 x2 Ht l2 IH; induction l1 as [ | u1 l1]; 
  intros x1 x2 Ht [ | u2 l2] IH; simpl; trivial; try discriminate IH.
  simpl in IH.
  case_eq (Oeset.compare OD u1 u2); intro Hu; rewrite Hu in IH;
  try discriminate IH.
  rewrite (Oeset.compare_eq_1 _ _ _ _ (join_eq_1 _ _ _ Ht)).
  rewrite <- (Oeset.compare_eq_2 _ _ _ _ (join_eq_2 _ _ _ Hu)).
  rewrite Oeset.compare_eq_refl.
  unfold d_join_list in IHl1; rewrite IHl1; trivial.
Qed.

Lemma in_brute_left_join_list :
  forall t s1 s2,
    In t (brute_left_join_list s1 s2) <->
    (exists x1 x2 : data, In x1 s1 /\ In x2 s2 /\ t =  join x1 x2).
Proof.
intros t s1 s2; rewrite brute_left_join_list_unfold, in_theta_join_list.
split; intros [x1 [x2 [Hx1 [Hx2 H]]]]; exists x1; exists x2; repeat split; trivial.
apply (proj2 H).
Qed.

Lemma N_join_list_1 :
  forall e s, 
    (forall x, Oeset.compare OD (join x e) x = Eq) ->
    comparelA (fun x y => Oeset.compare OD x y) (N_join_list e (s :: nil)) s = Eq.
Proof.
intros e s join_empty_2; simpl.
unfold brute_left_join_list.
rewrite theta_join_list_unfold; simpl.
induction s as [ | x1 s]; [apply refl_equal | simpl].
rewrite join_empty_2; apply IHs.
Qed.

Fixpoint N_join empty_d (lt : list data) : data :=
  match lt with
    | nil => empty_d 
    | x1 :: lt => join x1 (N_join empty_d lt)
  end.

Lemma N_join_unfold :
  forall e lt, N_join e lt = 
               match lt with
               | nil => e
               | x1 :: lt => join x1 (N_join e lt)
               end.
Proof.
intros e lt; case lt; intros; apply refl_equal.
Qed.

Lemma in_N_join_list :
  forall t e ll, In t (N_join_list e ll) <->
               (exists llt, (forall si ti, List.In (si, ti) llt -> In ti si) /\
                            List.map (@fst _ _) llt = ll /\
                            t = N_join e (List.map (@snd _ _) llt)).
Proof.
intros t e ll; revert t.
induction ll as [ | s1 ll]; intro t; rewrite N_join_list_unfold; split.
- intro H; simpl in H; destruct H as [H | H]; [ | contradiction H].
  subst t; exists nil; repeat split; intros; contradiction.
- intros [llt [H1 [H2 H3]]].
  destruct llt; [ | discriminate H2].
  simpl in H3; left; apply sym_eq; apply H3.
- rewrite in_brute_left_join_list.
  intros [x1 [x2 [Hx1 [Hx2 Ht]]]].
  rewrite IHll in Hx2.
  destruct Hx2 as [llt [H1 [H2 H3]]].
  exists ((s1, x1) :: llt); repeat split.
  + intros si ti Hi; simpl in Hi; destruct Hi as [Hi | Hi]; [ | apply H1; assumption].
    injection Hi; clear Hi; do 2 intro; subst; assumption.
  + simpl; apply f_equal; assumption.
  + rewrite Ht, H3; apply refl_equal.
- intros [llt [H1 [H2 H3]]].
  destruct llt as [ | [_s1 x1] llt]; [discriminate H2 | ].
  simpl in H2; injection H2; clear H2; intro H2; intro; subst _s1.
  rewrite in_brute_left_join_list.
  exists x1; exists (N_join e (map (snd (B:=data)) llt)); repeat split.
  + apply H1; left; apply refl_equal.
  + rewrite IHll; exists llt; repeat split; trivial.
    do 3 intro; apply H1; right; assumption.
  + rewrite H3; apply refl_equal.
Qed.

End Sec.


