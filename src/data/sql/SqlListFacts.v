(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**                    Facts for exact ordered SQL observations                     *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List NArith Lia Sorting.Permutation.

Require Import OrderedSet FiniteBag FiniteCollection FlatData SqlOrder
        SqlQuerySemantics.

Section Sec.

Hypothesis T : Tuple.Rcd.

Import Tuple.

Local Definition tuple := tuple T.

(** A concrete witness that every finite input has at least one legal ORDER BY
    observation.  The exact semantics remains relational: this insertion sort
    selects one witness only; it does not collapse tied legal permutations to
    a deterministic query result. *)
Fixpoint insert_ordered_row
    (value_is_null : value T -> bool)
    (keys : list (sort_key T))
    (row : tuple) (rows : list tuple) : list tuple :=
  match rows with
  | nil => row :: nil
  | head :: tail =>
      match compare_order_keys value_is_null keys row head with
      | Gt => head :: insert_ordered_row value_is_null keys row tail
      | Eq | Lt => row :: rows
      end
  end.

Fixpoint sort_ordered_rows
    (value_is_null : value T -> bool)
    (keys : list (sort_key T))
    (rows : list tuple) : list tuple :=
  match rows with
  | nil => nil
  | row :: tail =>
      insert_ordered_row value_is_null keys row
        (sort_ordered_rows value_is_null keys tail)
  end.

Lemma compare_order_value_opposite :
  forall value_is_null value_compare,
    (forall left right,
      value_compare left right = CompOpp (value_compare right left)) ->
    forall direction nulls left right,
      @compare_order_value T value_is_null value_compare
        direction nulls left right =
      CompOpp (@compare_order_value T value_is_null value_compare
        direction nulls right left).
Proof.
intros value_is_null value_compare Hcompare direction nulls left right.
unfold compare_order_value.
destruct (value_is_null left) eqn:Hleft;
  destruct (value_is_null right) eqn:Hright; simpl.
- reflexivity.
- now destruct nulls.
- now destruct nulls.
- destruct direction; simpl.
  + apply Hcompare.
  + rewrite (Hcompare left right).
    now destruct (value_compare right left).
Qed.

Lemma compare_order_key_opposite :
  forall value_is_null key left right,
    @compare_order_key T value_is_null key left right =
    CompOpp (@compare_order_key T value_is_null key right left).
Proof.
intros value_is_null
  [attribute direction nulls value_compare Hcompare] left right.
unfold compare_order_key; simpl.
now apply compare_order_value_opposite.
Qed.

Lemma compare_order_keys_opposite :
  forall value_is_null keys left right,
    @compare_order_keys T value_is_null keys left right =
    CompOpp (@compare_order_keys T value_is_null keys right left).
Proof.
intros value_is_null keys; induction keys as [|key rest IH];
  intros left right; simpl; [reflexivity|].
rewrite compare_order_key_opposite.
destruct (@compare_order_key T value_is_null key right left); simpl;
  [apply IH | reflexivity | reflexivity].
Qed.

Lemma ordered_pair_reverse_of_gt :
  forall value_is_null keys left right,
    @compare_order_keys T value_is_null keys left right = Gt ->
    @ordered_pair T value_is_null keys right left.
Proof.
intros value_is_null keys left right Hcompare.
unfold ordered_pair.
pose proof
  (@compare_order_keys_opposite value_is_null keys left right) as Hopposite.
rewrite Hcompare in Hopposite.
destruct (@compare_order_keys T value_is_null keys right left);
  simpl in Hopposite; try discriminate; trivial.
Qed.

Lemma insert_ordered_row_permutation :
  forall value_is_null keys row rows,
    Permutation (row :: rows)
      (insert_ordered_row value_is_null keys row rows).
Proof.
intros value_is_null keys row rows.
induction rows as [|head tail IH]; simpl; [apply Permutation_refl|].
destruct (@compare_order_keys T value_is_null keys row head) eqn:Hcompare;
  simpl; try apply Permutation_refl.
eapply Permutation_trans.
- apply perm_swap.
- now apply perm_skip.
Qed.

Lemma sort_ordered_rows_permutation :
  forall value_is_null keys rows,
    Permutation rows (sort_ordered_rows value_is_null keys rows).
Proof.
intros value_is_null keys rows; induction rows as [|row tail IH]; simpl.
- apply Permutation_refl.
- eapply Permutation_trans with
      (l' := row :: sort_ordered_rows value_is_null keys tail).
  + now apply perm_skip.
  + apply insert_ordered_row_permutation.
Qed.

Lemma insert_ordered_row_is_ordered :
  forall value_is_null keys row rows,
    @ordered_rows T value_is_null keys rows ->
    @ordered_rows T value_is_null keys
      (insert_ordered_row value_is_null keys row rows).
Proof.
intros value_is_null keys row rows.
induction rows as [|head tail IH]; intro Hordered; simpl; [trivial|].
destruct (@compare_order_keys T value_is_null keys row head) eqn:Hrow_head;
  simpl.
- split; [unfold ordered_pair; now rewrite Hrow_head|exact Hordered].
- split; [unfold ordered_pair; now rewrite Hrow_head|exact Hordered].
- destruct tail as [|next rest].
  + simpl; split; [now apply ordered_pair_reverse_of_gt|trivial].
  + simpl in Hordered; destruct Hordered as [Hhead_next Htail].
    specialize (IH Htail).
    simpl in IH.
    destruct (@compare_order_keys T value_is_null keys row next)
      eqn:Hrow_next.
    * cbn [insert_ordered_row]; rewrite Hrow_next; cbn [ordered_rows].
      repeat split; try assumption.
      -- now apply ordered_pair_reverse_of_gt.
      -- unfold ordered_pair; now rewrite Hrow_next.
    * cbn [insert_ordered_row]; rewrite Hrow_next; cbn [ordered_rows].
      repeat split; try assumption.
      -- now apply ordered_pair_reverse_of_gt.
      -- unfold ordered_pair; now rewrite Hrow_next.
    * cbn [insert_ordered_row]; rewrite Hrow_next; cbn [ordered_rows].
      split; assumption.
Qed.

Lemma sort_ordered_rows_is_ordered :
  forall value_is_null keys rows,
    @ordered_rows T value_is_null keys
      (sort_ordered_rows value_is_null keys rows).
Proof.
intros value_is_null keys rows; induction rows as [|row tail IH];
  simpl; [trivial|].
now apply insert_ordered_row_is_ordered.
Qed.

Lemma permutation_preserves_oeset_occurrences :
  forall first second,
    Permutation first second ->
    forall target,
      Oeset.nb_occ (OTuple T) target first =
      Oeset.nb_occ (OTuple T) target second.
Proof.
intros first second Hpermutation.
induction Hpermutation; intro target; simpl.
- reflexivity.
- now rewrite IHHpermutation.
- destruct (Oeset.compare (OTuple T) target x);
    destruct (Oeset.compare (OTuple T) target y); simpl; lia.
- now rewrite IHHpermutation1, IHHpermutation2.
Qed.

Lemma permutation_same_rows_as_bag :
  forall input output : list tuple,
    Permutation input output ->
    query_same_rows_as_bag output (query_rows_bag input).
Proof.
intros input output Hpermutation.
unfold query_same_rows_as_bag, query_rows_bag.
rewrite Febag.nb_occ_equal; intro target.
rewrite 2 Febag.nb_occ_mk_bag.
symmetry; now apply permutation_preserves_oeset_occurrences.
Qed.

Theorem order_by_rows_has_observation :
  forall value_is_null keys input,
    exists output,
      @order_by_rows T value_is_null keys input output.
Proof.
intros value_is_null keys input.
exists (sort_ordered_rows value_is_null keys input).
split.
- now apply permutation_same_rows_as_bag, sort_ordered_rows_permutation.
- apply sort_ordered_rows_is_ordered.
Qed.

End Sec.
