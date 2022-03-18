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
Require Import FTerms.
Require Import ATerms.
Require Import Env.
Require Import Interp.

Import Tuple.

Section Sec.

Hypothesis T : Rcd.

Notation value := (value T).
Notation attribute := (attribute T).
Notation tuple := (tuple T).
Notation aggterm := (aggterm T).
Arguments funterm {T}.
Arguments Group_Fine {T}.
Arguments Group_By {T}.
Arguments F_Dot {T}.
Arguments A_Expr {T}.
Arguments dot {r}.
Arguments mk_tuple {r}.

Inductive select : Type := 
  | Select_As : aggterm -> attribute -> select.

Inductive _select_list : Type :=
  | _Select_List : list select -> _select_list.

Inductive select_item : Type :=
  | Select_Star 
  | Select_List : _select_list -> select_item.

Definition pair_of_select x :=
  match x with
    | Select_As e a => (a, e)
  end.

Definition pairs_of_selects sl := match sl with _Select_List l => map pair_of_select l end.
Notation attaggs := (list (attribute T * aggterm T))%type.

Coercion pairs_of_selects : _select_list >-> attaggs.

Definition select_of_pair x :=
  match x with
    | (a, e) => Select_As e a
  end.

Definition selects_of_pairs l := (map select_of_pair l).

Definition sort_of_select_list (las : _select_list) :=
  match las with
    | _Select_List las => List.map (fun x => match x with Select_As _ a => a end) las
  end.

Definition projection (env : env T) (las : select_item) :=
  match las with
    | Select_Star => 
      match env with
        | nil => default_tuple _ (Fset.empty _)
        | (sa, gby, l) :: _ =>
          match quicksort (OTuple T) l with
          | nil => default_tuple _ (Fset.empty _)
          | t :: _ => t
          end
      end
    | Select_List las =>
        mk_tuple  
          (Fset.mk_set (A T) (sort_of_select_list las))
          (fun a => 
             match Oset.find (OAtt T) a las with 
             | Some e => interp_aggterm T env e
             | None => dot (default_tuple _ (Fset.empty _)) a
             end)
  end.

Lemma projection_eq :
  forall s env1 env2, equiv_env T env1 env2 -> projection env1 s =t= projection env2 s.
Proof.
intros s env1 env2 He; unfold projection.
destruct s as [ | s].
- destruct env1 as [ | [[sa1 gb1] x1] env1]; destruct env2 as [ | [[sa2 gb2] x2] env2];
  try inversion He.
  + apply Oeset.compare_eq_refl.
  + subst.
    simpl in H2; destruct H2 as [Hsa [Hg Hx]].
    rewrite compare_list_t in Hx; unfold compare_OLA in Hx.
    destruct (quicksort (OTuple T) x1) as [ | u1 l1]; 
      destruct (quicksort (OTuple T) x2) as [ | u2 l2]; try discriminate Hx;
    [apply Oeset.compare_eq_refl | simpl in Hx].
    case_eq (Oeset.compare (OTuple T) u1 u2); 
            intro Hu; rewrite Hu in Hx; try discriminate Hx; trivial.
- apply mk_tuple_eq_2.
  intros a Ha.
  case_eq (Oset.find (OAtt T) a s); [ | intros; apply refl_equal].
  intros; apply interp_aggterm_eq; trivial.
Qed.

Lemma labels_projection :
  forall env l, labels T (projection env (Select_List (_Select_List l))) =S=
                Fset.mk_set _ (map (fun x => match x with Select_As _ a => a end) l).
Proof.
intros env l; unfold projection, sort_of_select_list.
rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
apply Fset.equal_refl.
Qed.

Lemma labels_projection_app :
  forall env l1 l2,
    labels T (projection env (Select_List (_Select_List (l1 ++ l2)))) =S=    
    (labels T (projection env (Select_List (_Select_List l1))) unionS   
           labels T (projection env (Select_List (_Select_List l2)))).
Proof.
intros env l1 l2.
rewrite (Fset.equal_eq_1 _ _ _ _ (labels_projection _ _)), map_app,
   (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_app _ _ _)); 
  apply Fset.union_eq;
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_projection _ _)); apply Fset.equal_refl.
Qed.

Lemma projection_app : 
  forall env l1 l2, 
    projection env (Select_List (_Select_List (l1 ++ l2))) =t=
    join_tuple T (projection env (Select_List (_Select_List l1))) 
               (projection env (Select_List (_Select_List l2))).
Proof.
intros env l1 l2; unfold join_tuple; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)); apply labels_projection_app.
- intros a Ha; rewrite dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_projection_app _ _ _)) in Ha; rewrite Ha.
  case_eq (a inS? labels T (projection env (Select_List (_Select_List l1)))); intro Ka.
  + rewrite (Fset.mem_eq_2 _ _ _ (labels_projection _ _)) in Ka.
    unfold projection, sort_of_select_list; rewrite !dot_mk_tuple, Ka.
    rewrite map_app, Fset.mem_mk_set_app, Ka; simpl; rewrite map_app, Oset.find_app.
    case_eq (Oset.find (OAtt T) a (map pair_of_select l1)); [intros; apply refl_equal | ].
    intro Abs; apply False_rec.
    apply (Oset.find_none_alt (OAtt T) a _ Abs); 
      rewrite <- (Oset.mem_bool_true_iff (OAtt T)), <- Ka, Fset.mem_mk_set, map_map.
    apply f_equal; rewrite <- map_eq; intros [] _; apply refl_equal.
  + rewrite Fset.mem_union, Ka, Bool.Bool.orb_false_l in Ha.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_projection _ _)) in Ha.
    rewrite (Fset.mem_eq_2 _ _ _ (labels_projection _ _)) in Ka.
    unfold projection, sort_of_select_list; rewrite !dot_mk_tuple, map_app, Fset.mem_mk_set_app.
    rewrite Ha, Ka, Bool.Bool.orb_true_r; simpl.
    rewrite map_app, Oset.find_app.
    case_eq (Oset.find (OAtt T) a (map pair_of_select l1)); [ | intros; apply refl_equal].
    intros e He; apply False_rec.
    rewrite <- Bool.Bool.not_true_iff_false in Ka; apply Ka.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    assert (Ke := Oset.find_some _ _ _ He); rewrite in_map_iff in Ke.
    destruct Ke as [[_e _a] [_Ke Ke]]; injection _Ke; do 2 intro; subst.
    eexists; split; [ | apply Ke]; apply refl_equal.
Qed.

Lemma dot_projection :
  forall env l a e, In (Select_As e a) l -> all_diff (map fst (map pair_of_select l)) ->
    dot (projection env (Select_List (_Select_List l))) a = interp_aggterm T env e.
Proof.
intros env l a e H D; unfold projection; rewrite dot_mk_tuple.
assert (Ha : a inS Fset.mk_set (A T) (sort_of_select_list (_Select_List l))).
{
  simpl; rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  eexists; split; [ | apply H]; apply refl_equal.
}
rewrite Ha; simpl.
rewrite (Oset.all_diff_fst_find (OAtt T) _ a e D); [apply refl_equal | ].
rewrite in_map_iff; eexists; split; [ | apply H]; apply refl_equal.
Qed.

Definition to_direct_renaming (ll : list (attribute * attribute)) := 
  _Select_List (map (fun x => match x with (a, b) => Select_As (A_Expr (F_Dot a)) b end) ll).

Lemma to_direct_renaming_unfold_alt : 
  forall ll, to_direct_renaming (map (fun x => match x with (x1, x2) => (x2, x1) end) ll) =
  _Select_List (map (fun x => match x with (a, b) => Select_As (A_Expr (F_Dot b)) a end) ll).
Proof.
intro ll; unfold to_direct_renaming; apply f_equal; rewrite map_map, <- map_eq.
intros [a b] _; apply refl_equal.
Qed.

Lemma projection_renaming :
  forall env ss t, 
    Oset.permut (OAtt T) (map fst ss) ({{{labels T t}}}) ->
    all_diff (map snd ss) ->
    projection (env_t T env t) (Select_List (to_direct_renaming ss)) =t= 
    rename_tuple T (apply_renaming T ss) t.
Proof.
intros env ss t Hp Hs.
assert (Hf : all_diff (map fst ss)).
{
  refine (Oset.all_diff_permut_all_diff _ (Oset.permut_sym Hp)).
  apply Fset.all_diff_elements.
}
unfold projection, rename_tuple, sort_of_select_list, to_direct_renaming, apply_renaming.
rewrite map_map; apply mk_tuple_eq.
- rewrite Fset.equal_spec; intro a; unfold Fset.map; rewrite !Fset.mem_mk_set.
  apply Oset.permut_mem_bool_eq; apply Oset.nb_occ_permut; intro b.
  refine (eq_trans _ (Oset.nb_occ_map_eq_3 _ _ _ _ _ (fun x => Oset.permut_nb_occ x Hp) _)).
  rewrite !map_map; apply f_equal.
  rewrite <- map_eq; intros [a1 b1] H1; simpl.
  rewrite (Oset.all_diff_fst_find (OAtt T) _ _ _ Hf H1); apply refl_equal.
- intros b Hb Kb; simpl; unfold pair_of_select; rewrite map_map.
  rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff in Hb.
  destruct Hb as [[a _b] [_Hb Hb]]; subst _b.
  assert (Ha : a inS (labels T t)).
  {
    rewrite Fset.mem_elements, <- (Oset.permut_mem_bool_eq _ Hp), 
       Oset.mem_bool_true_iff, in_map_iff.
    eexists; split; [ | apply Hb]; apply refl_equal.
  }
  rewrite (Oset.all_diff_fst_find (OAtt T) _ b (A_Expr (F_Dot a))),
     (Oset.all_diff_fst_find (OAtt T) _ b (dot t a)).
  + simpl; rewrite Ha; apply refl_equal.
  + rewrite map_map; simpl.
    apply (Oset.all_diff_permut_all_diff (OA := OAtt T) Hs).
    apply Oset.permut_trans with
        (map  (fun x : attribute => match Oset.find (OAtt T) x ss with
                               | Some b0 => b0
                               | None => x
                               end) (map fst ss)).
    * rewrite map_map; apply Oset.permut_refl_alt2.
      rewrite <- map_eq; intros [a1 b1] H1; simpl.
      rewrite (Oset.all_diff_fst_find _ ss a1 b1 Hf H1); apply refl_equal.
    * apply _permut_map with eq.
      -- intros; subst; apply Oset.compare_eq_refl.
      -- revert Hp; apply _permut_incl.
         do 2 intro; rewrite Oset.compare_eq_iff; exact (fun h => h).
  + rewrite in_map_iff; exists a; split.
    * apply f_equal2; [ | apply refl_equal].
      rewrite (Oset.all_diff_fst_find (OAtt T) _ a b Hf Hb); apply refl_equal.
    * apply Fset.mem_in_elements; assumption.
  + rewrite map_map; simpl.
    apply (all_diff_eq Hs); rewrite <- map_eq; intros [] _; apply refl_equal.
  + rewrite in_map_iff.
    eexists; split; [ | apply Hb]; simpl; apply refl_equal.
Qed.

Definition id_renaming s : list select :=
  List.map (fun a => Select_As (A_Expr (F_Dot a)) a) (Fset.elements (A T) s).

Lemma projection_id_env_t :
 forall env sa t,  labels T t =S= sa ->
        projection (env_t T env t) (Select_List (_Select_List (id_renaming sa))) =t= t.
Proof.
intros env sa t Ht; unfold id_renaming; simpl.
rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), !map_map, map_id; 
  [ | trivial].
rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_idem _ _)), (Fset.equal_eq_2 _ _ _ _ Ht).
split; [apply Fset.equal_refl | ].
intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
unfold pair_of_select; rewrite dot_mk_tuple, Ha, Oset.find_map.
- rewrite Fset.mem_mk_set, <- Fset.mem_elements in Ha.
  simpl; rewrite (Fset.mem_eq_2 _ _ _ Ht), Ha; apply refl_equal.
- rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha; apply Ha.
Qed.

Definition restrict_env_slice s (es : env_slice T) :=
  match es with
  | (sa, g, l) => 
      (s, g, List.map (fun t => mk_tuple s (dot t)) l)
  end.

Definition extend_env_slice env s (es : env_slice T) :=
  match es with
  | (_, Group_Fine, _) => es
  | (sa, Group_By g, l) => 
    let sg := List.map (fun x => match x with (a, e) => Select_As e a end) (combine s g) in
    (sa unionS Fset.mk_set (A T) s,
     Group_By (List.map (fun a => A_Expr (F_Dot a)) s),
     List.map (fun t => projection (env_t T env t) (Select_List (_Select_List (id_renaming sa ++ sg)))) l)
  end.

Lemma restrict_env_slice_unfold :
  forall s es, restrict_env_slice s es =
  match es with
  | (sa, g, l) => 
      (s, g, List.map (fun t => mk_tuple s (dot t)) l)
  end.
Proof.
intros s [[sa g] l]; apply refl_equal.
Qed.                   

Lemma extend_env_slice_unfold :
  forall env s es, extend_env_slice env s es =
  match es with
  | (_, Group_Fine, _) => es
  | (sa, Group_By g, l) => 
    let sg := List.map (fun x => match x with (a, e) => Select_As e a end) (combine s g) in
    (sa unionS Fset.mk_set (A T) s,
     Group_By (List.map (fun a => A_Expr (F_Dot a)) s),
     List.map (fun t => projection (env_t T env t) (Select_List (_Select_List (id_renaming sa ++ sg)))) l)
  end.
Proof.
intros env s [[sa [g | ]] l]; apply refl_equal.
Qed.                   
    
(*



Lemma to_direct_renaming_unfold : 
  forall ll, to_direct_renaming ll =
  map (fun x => match x with (a, b) => Select_As (A_Expr T (F_Dot T a)) b end) ll.
Proof.
intro ll; apply refl_equal.
Qed.






Lemma projection_id_env_g :
 forall env esq sa, 
   (forall t, In t esq -> labels T t =S= sa) ->
   let p := (partition (mk_olists (OVal T))
            (fun t0 : tuple T =>
             map (fun f  => interp_aggterm T (env_t T env t0) f)
               (map (fun a : attribute T => A_Expr T (F_Dot T a)) ({{{sa}}}))) esq) in
  forall x v l, In (v, l) p -> In x l ->
        projection
          (env_g T env (Group_By T (map (fun a : attribute T => A_Expr T (F_Dot T a)) ({{{sa}}}))) l)
          (Select_List (id_renaming sa)) =t= x.
Proof.
intros env esq sa W p x v l Hl Hx; unfold p in *.
assert (Wx := W x (in_partition _ _ _ _ _ _ Hl Hx)).
assert (K : forall y, In y l -> y =t= x).
{
  intros y Hy.
  assert (Wy := W y (in_partition _ _ _ _ _ _ Hl Hy)).
  rewrite tuple_eq, Fset.equal_spec; split.
  - rewrite Fset.equal_spec in Wx, Wy; intro; rewrite Wx, Wy; apply refl_equal.
  - intros a Ha.
    rewrite (Fset.mem_eq_2 _ _ _ Wy) in Ha.
    assert (H := partition_homogeneous_values _ _ _ _ _ Hl _ Hy).
    rewrite <- (partition_homogeneous_values _ _ _ _ _ Hl _ Hx) in H.
    rewrite !map_map, <- map_eq in H.
    assert (Ka := H a); simpl in Ka.
    rewrite (Fset.mem_eq_2 _ _ _ Wx), (Fset.mem_eq_2 _ _ _ Wy), Ha in Ka.
    apply Ka; apply Fset.mem_in_elements; assumption.
}
unfold id_renaming; simpl; rewrite !map_map, map_id; [ | intros; apply refl_equal].
rewrite tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
  (Fset.equal_eq_1 _ _ _ _ (Fset.mk_set_idem _ _)), (Fset.equal_eq_2 _ _ _ _ Wx); split;
  [apply Fset.equal_refl | ].
intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
rewrite dot_mk_tuple, Ha.
rewrite Oset.find_map; [ | rewrite  Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha; apply Ha].
rewrite (Fset.mem_eq_2 _ _ _ (Fset.mk_set_idem _ _)) in Ha.
simpl.
rewrite (In_quicksort (OTuple T)) in Hx.
case_eq (quicksort (OTuple T) l); [intro Q; rewrite Q in Hx; contradiction Hx | ].
intros x1 q1 Q.
assert (Hx1 : x1 =t= x).
{
  apply K; rewrite (In_quicksort (OTuple T)), Q; left; apply refl_equal.
}
rewrite tuple_eq in Hx1.
rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)), (Fset.mem_eq_2 _ _ _ Wx), Ha.
apply (proj2 Hx1).
rewrite (Fset.mem_eq_2 _ _ _ (proj1 Hx1)), (Fset.mem_eq_2 _ _ _ Wx), Ha; apply refl_equal.
Qed.
*)

End Sec.
