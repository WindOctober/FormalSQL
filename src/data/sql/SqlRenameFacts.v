(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**             Support-local attribute, tuple, row, and outcome renaming          *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Sorting.Permutation.

Require Import BasicFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData
        SqlOutcome SqlBagAbstraction.

(** This module deliberately reuses [Tuple.rename_tuple].  It adds the explicit
    collision, typing, collection, and SQL-outcome contracts needed by query-level
    alpha-renaming; it introduces neither a second tuple representation nor a
    second query syntax. *)

Section RenameFacts.

Hypothesis T : Tuple.Rcd.

Import Tuple.

Local Definition tuple := tuple T.
Local Definition setA := Fset.set (A T).
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

(** Injectivity is required only on the labels observed by the surrounding
    operation.  This is the precise premise that prevents two distinct columns
    from being collapsed by [rename_tuple]. *)
Definition attribute_rename_injective_on
    (support : setA) (rho : attribute T -> attribute T) : Prop :=
  forall left right,
    left inS support ->
    right inS support ->
    rho left = rho right ->
    left = right.

(** Attribute types include any concrete type modifiers carried by the tuple
    instance.  Renaming must preserve that full type, not merely a coarse SQL
    type family. *)
Definition attribute_rename_type_preserving_on
    (support : setA) (rho : attribute T -> attribute T) : Prop :=
  forall source,
    source inS support ->
    type_of_attribute T (rho source) = type_of_attribute T source.

Definition attribute_rename_sound_on
    (support : setA) (rho : attribute T -> attribute T) : Prop :=
  attribute_rename_injective_on support rho /\
  attribute_rename_type_preserving_on support rho.

(** A fresh output remains distinct from every renamed label in [support]. *)
Definition attribute_rename_fresh_for
    (support : setA) (rho : attribute T -> attribute T)
    (fresh : attribute T) : Prop :=
  forall source,
    source inS support ->
    rho source <> rho fresh.

(** This cross-support condition is stronger than separately proving
    injectivity on [left] and [right].  It is the condition needed by joins and
    other operators for which a new collision between the two inputs is
    observable.  An attribute originally present in both supports may of course
    remain shared. *)
Definition attribute_rename_collision_free_between
    (left right : setA) (rho : attribute T -> attribute T) : Prop :=
  forall left_attribute right_attribute,
    left_attribute inS left ->
    right_attribute inS right ->
    rho left_attribute = rho right_attribute ->
    left_attribute = right_attribute.

Lemma attribute_rename_injective_on_identity :
  forall support,
    attribute_rename_injective_on support (fun attribute => attribute).
Proof.
intros support left right _ _ Hequal; exact Hequal.
Qed.

Lemma attribute_rename_type_preserving_on_identity :
  forall support,
    attribute_rename_type_preserving_on support (fun attribute => attribute).
Proof.
intros support source _; reflexivity.
Qed.

Lemma attribute_rename_map_identity :
  forall support,
    Fset.map (A T) (A T) (fun attribute => attribute) support =S= support.
Proof.
intro support.
rewrite Fset.equal_spec; intro target.
rewrite eq_bool_iff; split; intro Hmember.
- rewrite Fset.mem_map in Hmember.
  destruct Hmember as [source [Hsource Hmember]].
  subst target; exact Hmember.
- rewrite Fset.mem_map.
  exists target; split; [reflexivity | exact Hmember].
Qed.

Lemma attribute_rename_map_compose :
  forall rho sigma support,
    Fset.map (A T) (A T) sigma
      (Fset.map (A T) (A T) rho support) =S=
    Fset.map (A T) (A T) (fun attribute => sigma (rho attribute)) support.
Proof.
intros rho sigma support.
rewrite Fset.equal_spec; intro target.
rewrite eq_bool_iff; split; intro Hmember.
- rewrite Fset.mem_map in Hmember.
  destruct Hmember as [middle [Htarget Hmiddle]].
  rewrite Fset.mem_map in Hmiddle.
  destruct Hmiddle as [source [Hmiddle Hsource]].
  rewrite Fset.mem_map.
  exists source; split; [now rewrite Hmiddle | exact Hsource].
- rewrite Fset.mem_map in Hmember.
  destruct Hmember as [source [Htarget Hsource]].
  rewrite Fset.mem_map.
  exists (rho source); split; [exact Htarget |].
  rewrite Fset.mem_map.
  exists source; split; [reflexivity | exact Hsource].
Qed.

Lemma attribute_rename_injective_on_compose :
  forall rho sigma support,
    attribute_rename_injective_on support rho ->
    attribute_rename_injective_on
      (Fset.map (A T) (A T) rho support) sigma ->
    attribute_rename_injective_on support
      (fun attribute => sigma (rho attribute)).
Proof.
intros rho sigma support Hrho Hsigma left right Hleft Hright Hequal.
apply Hrho; [exact Hleft | exact Hright |].
apply Hsigma.
- rewrite Fset.mem_map; exists left; split; [reflexivity | exact Hleft].
- rewrite Fset.mem_map; exists right; split; [reflexivity | exact Hright].
- exact Hequal.
Qed.

Lemma attribute_rename_type_preserving_on_compose :
  forall rho sigma support,
    attribute_rename_type_preserving_on support rho ->
    attribute_rename_type_preserving_on
      (Fset.map (A T) (A T) rho support) sigma ->
    attribute_rename_type_preserving_on support
      (fun attribute => sigma (rho attribute)).
Proof.
intros rho sigma support Hrho Hsigma source Hsource.
rewrite Hsigma.
- apply Hrho; exact Hsource.
- rewrite Fset.mem_map.
  exists source; split; [reflexivity | exact Hsource].
Qed.

Lemma attribute_rename_collision_free_between_of_union :
  forall left right rho,
    attribute_rename_injective_on (left unionS right) rho ->
    attribute_rename_collision_free_between left right rho.
Proof.
intros left right rho Hinjective left_attribute right_attribute
  Hleft Hright Hequal.
apply Hinjective.
- rewrite Fset.mem_union, Hleft; reflexivity.
- rewrite Fset.mem_union, Hright, Bool.orb_true_r; reflexivity.
- exact Hequal.
Qed.

Lemma attribute_rename_fresh_for_of_union_injective :
  forall support rho fresh,
    ~ fresh inS support ->
    attribute_rename_injective_on
      (support unionS Fset.singleton (A T) fresh) rho ->
    attribute_rename_fresh_for support rho fresh.
Proof.
intros support rho fresh Hfresh Hinjective source Hsource Hequal.
apply Hfresh.
assert (Hsource_union : source inS
  (support unionS Fset.singleton (A T) fresh)).
{ rewrite Fset.mem_union, Hsource; reflexivity. }
assert (Hfresh_union : fresh inS
  (support unionS Fset.singleton (A T) fresh)).
{
  rewrite Fset.mem_union, Fset.singleton_spec, Oset.eq_bool_refl,
    Bool.orb_true_r; reflexivity.
}
pose proof
  (Hinjected := Hinjective source fresh Hsource_union Hfresh_union Hequal).
now subst fresh.
Qed.

(** A collision on two distinct supported labels is an explicit refutation of
    the soundness premise.  This abstracts the standard counterexample in which
    two different source values would compete for one renamed field. *)
Lemma attribute_rename_collision_rejects_injectivity :
  forall support rho left right,
    left inS support ->
    right inS support ->
    left <> right ->
    rho left = rho right ->
    ~ attribute_rename_injective_on support rho.
Proof.
intros support rho left right Hleft Hright Hdistinct Hcollision Hinjective.
apply Hdistinct; now apply (Hinjective left right Hleft Hright Hcollision).
Qed.

(** Generic row value conformance.  Concrete tuple instances may expose more
    specialized schema predicates, but this is the semantics-generic property
    required to show that a type-preserving alpha-renaming does not alter value
    types or type modifiers. *)
Definition tuple_well_typed (row : tuple) : Prop :=
  forall source,
    source inS labels T row ->
    type_of_value T (dot T row source) = type_of_attribute T source.

Lemma rename_tuple_labels_transport :
  forall rho row,
    labels T (rename_tuple T rho row) =S=
    Fset.map (A T) (A T) rho (labels T row).
Proof.
intros rho row; exact (proj1 (rename_tuple_ok T rho row)).
Qed.

Lemma rename_tuple_lookup_transport :
  forall rho row,
    attribute_rename_injective_on (labels T row) rho ->
    forall source,
      source inS labels T row ->
      dot T (rename_tuple T rho row) (rho source) = dot T row source.
Proof.
intros rho row Hinjective source Hsource.
exact (proj2 (rename_tuple_ok T rho row) Hinjective source Hsource).
Qed.

Lemma rename_tuple_value_transport :
  forall rho row source,
    attribute_rename_injective_on (labels T row) rho ->
    source inS labels T row ->
    dot T (rename_tuple T rho row) (rho source) = dot T row source.
Proof.
intros; now apply rename_tuple_lookup_transport.
Qed.

Lemma rename_tuple_identity :
  forall row,
    rename_tuple T (fun attribute => attribute) row =t= row.
Proof.
intro row.
pose proof (rename_tuple_labels_transport
  (fun attribute : attribute T => attribute) row) as Hrename_labels.
pose proof (attribute_rename_map_identity (labels T row)) as Hmap_identity.
assert (Hlabels :
  labels T (rename_tuple T (fun attribute => attribute) row) =S=
  labels T row).
{
  rewrite Fset.equal_spec in Hrename_labels, Hmap_identity |- *.
  intro attribute; now rewrite Hrename_labels, Hmap_identity.
}
rewrite tuple_eq; split; [exact Hlabels |].
intros source Hsource_renamed.
rewrite (Fset.mem_eq_2 _ _ _ Hlabels) in Hsource_renamed.
exact (@rename_tuple_lookup_transport
  (fun attribute : attribute T => attribute) row
  (attribute_rename_injective_on_identity (labels T row))
  source Hsource_renamed).
Qed.

Lemma rename_tuple_composition :
  forall rho sigma row,
    attribute_rename_injective_on (labels T row) rho ->
    attribute_rename_injective_on
      (Fset.map (A T) (A T) rho (labels T row)) sigma ->
    rename_tuple T sigma (rename_tuple T rho row) =t=
    rename_tuple T (fun attribute => sigma (rho attribute)) row.
Proof.
intros rho sigma row Hrho Hsigma.
set (middle := rename_tuple T rho row).
set (composed := fun attribute => sigma (rho attribute)).
pose proof (rename_tuple_labels_transport rho row) as Hmiddle_labels.
pose proof (rename_tuple_labels_transport sigma middle) as Hleft_labels.
pose proof (rename_tuple_labels_transport composed row) as Hright_labels.
pose proof (attribute_rename_map_compose rho sigma (labels T row))
  as Hmap_compose.
assert (Hsigma_middle :
  attribute_rename_injective_on (labels T middle) sigma).
{
  intros left right Hleft Hright Hequal.
  apply Hsigma.
  - rewrite <- (Fset.mem_eq_2 _ _ _ Hmiddle_labels); exact Hleft.
  - rewrite <- (Fset.mem_eq_2 _ _ _ Hmiddle_labels); exact Hright.
  - exact Hequal.
}
assert (Hcomposed :
  attribute_rename_injective_on (labels T row) composed).
{
  unfold composed.
  now apply attribute_rename_injective_on_compose.
}
assert (Hmapped_middle :
  Fset.map (A T) (A T) sigma (labels T middle) =S=
  Fset.map (A T) (A T) sigma
    (Fset.map (A T) (A T) rho (labels T row))).
{
  apply Fset.map_eq_s; exact Hmiddle_labels.
}
assert (Hlabels :
  labels T (rename_tuple T sigma middle) =S=
  labels T (rename_tuple T composed row)).
{
  rewrite Fset.equal_spec; intro target.
  rewrite (Fset.mem_eq_2 _ _ _ Hleft_labels),
    (Fset.mem_eq_2 _ _ _ Hmapped_middle),
    (Fset.mem_eq_2 _ _ _ Hmap_compose),
    <- (Fset.mem_eq_2 _ _ _ Hright_labels).
  reflexivity.
}
rewrite tuple_eq; split; [exact Hlabels |].
intros target Htarget.
rewrite (Fset.mem_eq_2 _ _ _ Hleft_labels) in Htarget.
rewrite Fset.mem_map in Htarget.
destruct Htarget as [middle_attribute [Htarget Hmiddle_attribute]].
rewrite (Fset.mem_eq_2 _ _ _ Hmiddle_labels) in Hmiddle_attribute.
rewrite Fset.mem_map in Hmiddle_attribute.
destruct Hmiddle_attribute as
  [source [Hmiddle_attribute Hsource]].
subst middle_attribute target.
assert (Hrho_source_middle : rho source inS labels T middle).
{
  rewrite (Fset.mem_eq_2 _ _ _ Hmiddle_labels), Fset.mem_map.
  exists source; split; [reflexivity | exact Hsource].
}
rewrite (@rename_tuple_lookup_transport sigma middle Hsigma_middle
  (rho source) Hrho_source_middle).
unfold middle.
rewrite (@rename_tuple_lookup_transport rho row Hrho source Hsource).
symmetry.
unfold composed.
exact (@rename_tuple_lookup_transport
  (fun attribute => sigma (rho attribute)) row Hcomposed source Hsource).
Qed.

Lemma rename_tuple_equivalence_transport :
  forall rho left right,
    left =t= right ->
    rename_tuple T rho left =t= rename_tuple T rho right.
Proof.
intros rho left right Hequal; now apply rename_tuple_eq.
Qed.

Lemma rename_tuple_equivalence_reflection :
  forall rho left right,
    attribute_rename_collision_free_between
      (labels T left) (labels T right) rho ->
    rename_tuple T rho left =t= rename_tuple T rho right ->
    left =t= right.
Proof.
intros rho left right Hcollision Hrenamed.
apply (proj2 (rename_tuple_inj T rho left right Hcollision)); exact Hrenamed.
Qed.

Lemma rename_tuple_equivalence_iff :
  forall rho left right,
    attribute_rename_collision_free_between
      (labels T left) (labels T right) rho ->
    (left =t= right <->
     rename_tuple T rho left =t= rename_tuple T rho right).
Proof.
intros rho left right Hcollision.
exact (rename_tuple_inj T rho left right Hcollision).
Qed.

Lemma rename_tuple_well_typed_transport :
  forall rho row,
    attribute_rename_injective_on (labels T row) rho ->
    attribute_rename_type_preserving_on (labels T row) rho ->
    tuple_well_typed row ->
    tuple_well_typed (rename_tuple T rho row).
Proof.
intros rho row Hinjective Htypes Htyped target Htarget.
rewrite (Fset.mem_eq_2 _ _ _ (rename_tuple_labels_transport rho row))
  in Htarget.
rewrite Fset.mem_map in Htarget.
destruct Htarget as [source [Hsource Hmember]].
subst target.
rewrite (@rename_tuple_lookup_transport rho row Hinjective source Hmember),
  (Htyped source Hmember), (Htypes source Hmember).
reflexivity.
Qed.

Definition rename_rows
    (rho : attribute T -> attribute T) (rows : list tuple) : list tuple :=
  map (rename_tuple T rho) rows.

Definition rename_bag
    (rho : attribute T -> attribute T) (bag : bagT) : bagT :=
  Febag.map BTupleT BTupleT (rename_tuple T rho) bag.

(** Exact ordered transport: the list shape and position of every row are
    retained, while hidden tuple representations are compared extensionally. *)
Definition rows_rename_equiv
    (rho : attribute T -> attribute T)
    (left right : list tuple) : Prop :=
  Forall2
    (fun left_row right_row =>
      rename_tuple T rho left_row =t= right_row)
    left right.

(** Query alpha-renaming also needs equality reflection across distinct row
    occurrences.  The support is phrased with setoid membership so equivalent
    tuple representatives cannot evade the collision check. *)
Definition rows_rename_collision_safe
    (rho : attribute T -> attribute T) (rows : list tuple) : Prop :=
  forall left right,
    Oeset.mem_bool (OTuple T) left rows = true ->
    Oeset.mem_bool (OTuple T) right rows = true ->
    attribute_rename_collision_free_between
      (labels T left) (labels T right) rho.

(** Declared query schemas do not constrain malformed VALUES or database bags.
    Query-level transport therefore records type preservation on every actual
    source-row label as well as on the syntactic output signature. *)
Definition rows_rename_type_safe
    (rho : attribute T -> attribute T) (rows : list tuple) : Prop :=
  forall row,
    Oeset.mem_bool (OTuple T) row rows = true ->
    attribute_rename_type_preserving_on (labels T row) rho.

(** A lossless ordered renaming has both the exact pointwise list relation and
    enough actual-row injection to prevent two tuple-equivalence classes from
    being merged. *)
Definition rows_rename_sound
    (rho : attribute T -> attribute T)
    (left right : list tuple) : Prop :=
  rows_rename_equiv rho left right /\
  rows_rename_collision_safe rho left /\
  rows_rename_type_safe rho left.

Lemma rows_rename_equiv_canonical :
  forall rho rows,
    rows_rename_equiv rho rows (rename_rows rho rows).
Proof.
intros rho rows; induction rows as [|row rows IH]; cbn [rename_rows].
- constructor.
- constructor; [apply Oeset.compare_eq_refl | exact IH].
Qed.

Lemma rows_rename_equiv_of_canonical_ordered :
  forall rho left right,
    ordered_rows_equiv T (rename_rows rho left) right ->
    rows_rename_equiv rho left right.
Proof.
intros rho left; induction left as [|left_row left_rows IH];
  intros [|right_row right_rows] Hequiv;
  unfold ordered_rows_equiv, mk_oelists in Hequiv; cbn in Hequiv;
  try discriminate.
- constructor.
- case_eq (Oeset.compare (OTuple T)
    (rename_tuple T rho left_row) right_row); intro Hrow;
    rewrite Hrow in Hequiv; try discriminate.
  constructor; [exact Hrow | now apply IH].
Qed.

Lemma rows_rename_sound_canonical :
  forall rho rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_type_safe rho rows ->
    rows_rename_sound rho rows (rename_rows rho rows).
Proof.
intros rho rows Hcollision Htypes; split.
- apply rows_rename_equiv_canonical.
- now split.
Qed.

Lemma rename_rows_identity :
  forall rows,
    rows_rename_equiv (fun attribute => attribute) rows rows.
Proof.
intro rows; induction rows as [|row rows IH].
- constructor.
- constructor; [apply rename_tuple_identity | exact IH].
Qed.

Lemma rows_rename_collision_safe_identity :
  forall rows,
    rows_rename_collision_safe
      (fun attribute => attribute) rows.
Proof.
intros rows left right _ _ left_attribute right_attribute
  _ _ Hequal; exact Hequal.
Qed.

Lemma rows_rename_type_safe_identity :
  forall rows,
    rows_rename_type_safe (fun attribute => attribute) rows.
Proof.
intros rows row _ source _; reflexivity.
Qed.

Lemma rows_rename_sound_identity :
  forall rows,
    rows_rename_sound (fun attribute => attribute) rows rows.
Proof.
intro rows; split.
- apply rename_rows_identity.
- split.
  + apply rows_rename_collision_safe_identity.
  + apply rows_rename_type_safe_identity.
Qed.

Lemma rename_rows_composition :
  forall rho sigma rows,
    (forall row,
      In row rows ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      In row rows ->
      attribute_rename_injective_on
        (Fset.map (A T) (A T) rho (labels T row)) sigma) ->
    rows_rename_equiv sigma (rename_rows rho rows)
      (rename_rows (fun attribute => sigma (rho attribute)) rows).
Proof.
intros rho sigma rows Hrho Hsigma.
induction rows as [|row rows IH]; cbn [rename_rows].
- constructor.
- constructor.
  + apply rename_tuple_composition.
    * apply Hrho; left; reflexivity.
    * apply Hsigma; left; reflexivity.
  + apply IH.
    * intros candidate Hcandidate; apply Hrho; right; exact Hcandidate.
    * intros candidate Hcandidate; apply Hsigma; right; exact Hcandidate.
Qed.

Lemma rename_rows_length :
  forall rho rows,
    length (rename_rows rho rows) = length rows.
Proof.
intros rho rows; unfold rename_rows; now rewrite length_map.
Qed.

Lemma rows_rename_equiv_length :
  forall rho left right,
    rows_rename_equiv rho left right ->
    length left = length right.
Proof.
intros rho left right Hrows; now apply Forall2_length in Hrows.
Qed.

Lemma rename_rows_firstn :
  forall rho count rows,
    rename_rows rho (firstn count rows) =
    firstn count (rename_rows rho rows).
Proof.
intros rho count; unfold rename_rows.
induction count as [|count IH]; intros [|row rows]; simpl; try reflexivity.
now rewrite IH.
Qed.

Lemma rename_rows_skipn :
  forall rho count rows,
    rename_rows rho (skipn count rows) =
    skipn count (rename_rows rho rows).
Proof.
intros rho count; unfold rename_rows.
induction count as [|count IH]; intros [|row rows]; simpl; try reflexivity.
now rewrite IH.
Qed.

Lemma rows_rename_equiv_firstn :
  forall rho count left right,
    rows_rename_equiv rho left right ->
    rows_rename_equiv rho (firstn count left) (firstn count right).
Proof.
intros rho count left right Hrows.
unfold rows_rename_equiv in *.
revert count; induction Hrows; intros [|count]; simpl.
- constructor.
- constructor.
- constructor.
- constructor; [exact H | now apply IHHrows].
Qed.

Lemma rows_rename_equiv_skipn :
  forall rho count left right,
    rows_rename_equiv rho left right ->
    rows_rename_equiv rho (skipn count left) (skipn count right).
Proof.
intros rho count left right Hrows.
unfold rows_rename_equiv in *.
revert count; induction Hrows; intros [|count]; simpl.
- constructor.
- constructor.
- constructor; assumption.
- now apply IHHrows.
Qed.

Lemma rows_rename_collision_safe_firstn :
  forall rho count rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_collision_safe rho (firstn count rows).
Proof.
intros rho count rows Hsafe left right Hleft Hright.
apply Hsafe.
- rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
    Bool.orb_true_iff.
  now left.
- rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
    Bool.orb_true_iff.
  now left.
Qed.

Lemma rows_rename_collision_safe_skipn :
  forall rho count rows,
    rows_rename_collision_safe rho rows ->
    rows_rename_collision_safe rho (skipn count rows).
Proof.
intros rho count rows Hsafe left right Hleft Hright.
apply Hsafe.
- rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
    Bool.orb_true_iff.
  now right.
- rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
    Bool.orb_true_iff.
  now right.
Qed.

Lemma rows_rename_type_safe_firstn :
  forall rho count rows,
    rows_rename_type_safe rho rows ->
    rows_rename_type_safe rho (firstn count rows).
Proof.
intros rho count rows Hsafe row Hrow.
apply Hsafe.
rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
  Bool.orb_true_iff.
now left.
Qed.

Lemma rows_rename_type_safe_skipn :
  forall rho count rows,
    rows_rename_type_safe rho rows ->
    rows_rename_type_safe rho (skipn count rows).
Proof.
intros rho count rows Hsafe row Hrow.
apply Hsafe.
rewrite <- (firstn_skipn count rows), Oeset.mem_bool_app,
  Bool.orb_true_iff.
now right.
Qed.

Lemma rows_rename_sound_firstn :
  forall rho count left right,
    rows_rename_sound rho left right ->
    rows_rename_sound rho (firstn count left) (firstn count right).
Proof.
intros rho count left right [Hrows [Hcollision Htypes]]; split.
- now apply rows_rename_equiv_firstn.
- split.
  + now apply rows_rename_collision_safe_firstn.
  + now apply rows_rename_type_safe_firstn.
Qed.

Lemma rows_rename_sound_skipn :
  forall rho count left right,
    rows_rename_sound rho left right ->
    rows_rename_sound rho (skipn count left) (skipn count right).
Proof.
intros rho count left right [Hrows [Hcollision Htypes]]; split.
- now apply rows_rename_equiv_skipn.
- split.
  + now apply rows_rename_collision_safe_skipn.
  + now apply rows_rename_type_safe_skipn.
Qed.

Lemma rows_rename_sound_reflects_equivalence :
  forall rho left_rows right_rows left right,
    rows_rename_sound rho left_rows right_rows ->
    Oeset.mem_bool (OTuple T) left left_rows = true ->
    Oeset.mem_bool (OTuple T) right left_rows = true ->
    rename_tuple T rho left =t= rename_tuple T rho right ->
    left =t= right.
Proof.
intros rho left_rows right_rows left right [_ [Hsafe _]]
  Hleft Hright Hrenamed.
apply (@rename_tuple_equivalence_reflection rho left right).
- now apply Hsafe.
- exact Hrenamed.
Qed.

Lemma rename_rows_permutation_transport :
  forall rho left right,
    Permutation left right ->
    Permutation (rename_rows rho left) (rename_rows rho right).
Proof.
intros rho left right Hpermutation.
unfold rename_rows; now apply Permutation_map.
Qed.

Lemma rename_rows_ordered_equiv_transport :
  forall rho left right,
    ordered_rows_equiv T left right ->
    ordered_rows_equiv T (rename_rows rho left) (rename_rows rho right).
Proof.
intros rho left.
induction left as [|left_row left_rows IH];
  intros [|right_row right_rows] Hequiv;
  unfold ordered_rows_equiv, mk_oelists in *; cbn in *;
  try discriminate; try reflexivity.
case_eq (Oeset.compare (OTuple T) left_row right_row);
  intro Hrow; rewrite Hrow in Hequiv; try discriminate.
pose proof (@rename_tuple_equivalence_transport rho left_row right_row Hrow)
  as Hrenamed_row.
change
  (comparelA (Oeset.compare (OTuple T))
    (rename_tuple T rho left_row :: rename_rows rho left_rows)
    (rename_tuple T rho right_row :: rename_rows rho right_rows) = Eq).
rewrite comparelA_unfold, Hrenamed_row.
now apply IH.
Qed.

(** Multiplicity is preserved only when the renaming reflects tuple equality
    between the distinguished row and every represented row. *)
Lemma rename_rows_multiplicity_transport :
  forall rho row rows,
    (forall candidate,
      Oeset.mem_bool (OTuple T) candidate rows = true ->
      attribute_rename_collision_free_between
        (labels T row) (labels T candidate) rho) ->
    Oeset.nb_occ (OTuple T) (rename_tuple T rho row)
      (rename_rows rho rows) =
    Oeset.nb_occ (OTuple T) row rows.
Proof.
intros rho row rows Hinjective.
unfold rename_rows.
apply nb_occ_map_rename_tuple.
intros left_attribute right_attribute candidate Hcandidate
  Hleft Hright Hequal.
exact (Hinjective candidate Hcandidate
  left_attribute right_attribute Hleft Hright Hequal).
Qed.

Lemma rows_rename_sound_multiplicity_transport :
  forall rho row rows,
    rows_rename_collision_safe rho rows ->
    Oeset.mem_bool (OTuple T) row rows = true ->
    Oeset.nb_occ (OTuple T) (rename_tuple T rho row)
      (rename_rows rho rows) =
    Oeset.nb_occ (OTuple T) row rows.
Proof.
intros rho row rows Hsafe Hrow.
apply rename_rows_multiplicity_transport.
intros candidate Hcandidate.
now apply Hsafe.
Qed.

Lemma rename_bag_multiplicity_transport :
  forall rho row bag,
    (forall candidate,
      candidate inBE bag ->
      attribute_rename_collision_free_between
        (labels T row) (labels T candidate) rho) ->
    Febag.nb_occ BTupleT (rename_tuple T rho row) (rename_bag rho bag) =
    Febag.nb_occ BTupleT row bag.
Proof.
intros rho row bag Hinjective.
unfold rename_bag, Febag.map.
rewrite Febag.nb_occ_mk_bag, Febag.nb_occ_elements.
apply nb_occ_map_rename_tuple.
intros left_attribute right_attribute candidate Hcandidate
  Hleft Hright Hequal.
apply (Hinjective candidate).
- unfold Febag.mem; exact Hcandidate.
- exact Hleft.
- exact Hright.
- exact Hequal.
Qed.

Lemma rename_rows_well_typed_transport :
  forall rho rows,
    Forall tuple_well_typed rows ->
    (forall row,
      In row rows ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      In row rows ->
      attribute_rename_type_preserving_on (labels T row) rho) ->
    Forall tuple_well_typed (rename_rows rho rows).
Proof.
intros rho rows Htyped Hinjective Htypes.
induction Htyped as [|row rows Hrow Hrows IH]; cbn [rename_rows].
- constructor.
- constructor.
  + apply rename_tuple_well_typed_transport.
    * apply Hinjective; left; reflexivity.
    * apply Htypes; left; reflexivity.
    * exact Hrow.
  + apply IH.
    * intros candidate Hcandidate; apply Hinjective; right; exact Hcandidate.
    * intros candidate Hcandidate; apply Htypes; right; exact Hcandidate.
Qed.

(** Deterministic outcome mapping retains the exact SQL error category and maps
    only successful ordered row observations. *)
Definition rename_query_outcome
    (rho : attribute T -> attribute T)
    (outcome : sql_outcome (list tuple)) : sql_outcome (list tuple) :=
  match outcome with
  | SqlSuccess rows => SqlSuccess (rename_rows rho rows)
  | SqlError error => SqlError error
  end.

Definition outcome_rename_equiv
    (rho : attribute T -> attribute T)
    (left right : sql_outcome (list tuple)) : Prop :=
  match left, right with
  | SqlSuccess left_rows, SqlSuccess right_rows =>
      rows_rename_equiv rho left_rows right_rows
  | SqlError left_error, SqlError right_error => left_error = right_error
  | _, _ => False
  end.

Lemma rename_query_outcome_success :
  forall rho rows,
    rename_query_outcome rho (SqlSuccess rows) =
    SqlSuccess (rename_rows rho rows).
Proof.
intros; reflexivity.
Qed.

Lemma rename_query_outcome_error :
  forall rho error,
    rename_query_outcome rho (SqlError error) = SqlError error.
Proof.
intros; reflexivity.
Qed.

Lemma outcome_rename_equiv_success :
  forall rho left right,
    outcome_rename_equiv rho (SqlSuccess left) (SqlSuccess right) <->
    rows_rename_equiv rho left right.
Proof.
intros; split; exact (fun hypothesis => hypothesis).
Qed.

Lemma outcome_rename_equiv_error :
  forall rho left_error right_error,
    outcome_rename_equiv rho (SqlError left_error) (SqlError right_error) <->
    left_error = right_error.
Proof.
intros; split; exact (fun hypothesis => hypothesis).
Qed.

Lemma outcome_rename_equiv_canonical :
  forall rho outcome,
    outcome_rename_equiv rho outcome (rename_query_outcome rho outcome).
Proof.
intros rho [rows|error]; simpl.
- apply rows_rename_equiv_canonical.
- reflexivity.
Qed.

Lemma rename_query_outcome_identity :
  forall outcome,
    outcome_rename_equiv (fun attribute => attribute) outcome outcome.
Proof.
intros [rows|error]; simpl.
- apply rename_rows_identity.
- reflexivity.
Qed.

Lemma rename_query_outcome_composition :
  forall rho sigma outcome,
    (forall row,
      match outcome with
      | SqlSuccess rows => In row rows
      | SqlError _ => False
      end ->
      attribute_rename_injective_on (labels T row) rho) ->
    (forall row,
      match outcome with
      | SqlSuccess rows => In row rows
      | SqlError _ => False
      end ->
      attribute_rename_injective_on
        (Fset.map (A T) (A T) rho (labels T row)) sigma) ->
    outcome_rename_equiv sigma (rename_query_outcome rho outcome)
      (rename_query_outcome
        (fun attribute => sigma (rho attribute)) outcome).
Proof.
intros rho sigma [rows|error] Hrho Hsigma; simpl in *.
- now apply rename_rows_composition.
- reflexivity.
Qed.

End RenameFacts.

Arguments attribute_rename_injective_on {T} _ _.
Arguments attribute_rename_type_preserving_on {T} _ _.
Arguments attribute_rename_sound_on {T} _ _.
Arguments attribute_rename_fresh_for {T} _ _ _.
Arguments attribute_rename_collision_free_between {T} _ _ _.
Arguments tuple_well_typed {T} _.
Arguments rename_rows {T} _ _.
Arguments rename_bag {T} _ _.
Arguments rows_rename_equiv {T} _ _ _.
Arguments rows_rename_collision_safe {T} _ _.
Arguments rows_rename_type_safe {T} _ _.
Arguments rows_rename_sound {T} _ _ _.
Arguments rename_query_outcome {T} _ _.
Arguments outcome_rename_equiv {T} _ _ _.
