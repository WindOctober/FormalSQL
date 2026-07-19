(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**           Possible-bag abstraction of exact ordered observations               *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List.

Require Import FiniteBag FiniteCollection FlatData SqlOutcome.

(** Ordered row-list outcomes are the single exact query semantics.  [alpha]
    maps them to possible bags; [gamma] forgets order by permutation closure
    and is therefore an over-approximation.  [BagClosed] characterizes exactly
    the observation relations for which this abstraction is complete for
    equivalence. *)

Section Sec.

Hypothesis T : Tuple.Rcd.

Import Tuple.

Local Definition tuple := tuple T.
Local Definition BTupleT := Fecol.CBag (CTuple T).
Local Definition bagT := Febag.bag BTupleT.

(** Relations are compared pointwise.  In particular, none of the results in
    this module requires functional or propositional extensionality. *)
Definition rel_equiv {A : Type} (left right : A -> Prop) : Prop :=
  forall value, left value <-> right value.

Definition rel_incl {A : Type} (left right : A -> Prop) : Prop :=
  forall value, left value -> right value.

(** FormalSQL bags are represented values, so their semantic equality is the
    finite-bag equality relation rather than Coq's Leibniz equality. *)
Definition bag_eq (left right : bagT) : Prop :=
  left =BE= right.

Lemma bag_eq_refl :
  forall bag, bag_eq bag bag.
Proof.
intro bag; unfold bag_eq; apply Febag.equal_refl.
Qed.

Lemma bag_eq_sym :
  forall left right, bag_eq left right -> bag_eq right left.
Proof.
intros left right Heq; unfold bag_eq in *; now apply Febag.equal_sym.
Qed.

Lemma bag_eq_trans :
  forall first second third,
    bag_eq first second -> bag_eq second third -> bag_eq first third.
Proof.
intros first second third Hfirst Hsecond.
unfold bag_eq in *.
eapply Febag.equal_trans; eassumption.
Qed.

Definition rows_bag (rows : list tuple) : bagT :=
  Febag.mk_bag BTupleT rows.

(** A possible-bag relation is semantic only when membership is invariant under
    [bag_eq].  This condition is essential because [bagT] is not a quotient. *)
Definition possible_bag_extensional (bags : bagT -> Prop) : Prop :=
  forall left right,
    bag_eq left right ->
    (bags left <-> bags right).

(** [alpha] forgets list order while retaining every possible result bag. *)
Definition alpha (observations : list tuple -> Prop) : bagT -> Prop :=
  fun bag =>
    exists rows,
      observations rows /\
      bag_eq (rows_bag rows) bag.

(** [gamma] admits every list representation of an allowed bag. *)
Definition gamma (bags : bagT -> Prop) : list tuple -> Prop :=
  fun rows => bags (rows_bag rows).

Definition permutation_closure
    (observations : list tuple -> Prop) : list tuple -> Prop :=
  gamma (alpha observations).

(** A list observation relation is bag-closed exactly when membership depends
    only on the represented bag. *)
Definition BagClosed (observations : list tuple -> Prop) : Prop :=
  forall left right,
    bag_eq (rows_bag left) (rows_bag right) ->
    (observations left <-> observations right).

Lemma alpha_extensional :
  forall observations,
    possible_bag_extensional (alpha observations).
Proof.
intros observations left right Heq.
unfold alpha.
split.
- intros [rows [Hrows Hleft]].
  exists rows; split; [exact Hrows |].
  eapply bag_eq_trans; eassumption.
- intros [rows [Hrows Hright]].
  exists rows; split; [exact Hrows |].
  eapply bag_eq_trans; [exact Hright |].
  now apply bag_eq_sym.
Qed.

Lemma observations_in_permutation_closure :
  forall observations,
    rel_incl observations (permutation_closure observations).
Proof.
intros observations rows Hrows.
unfold permutation_closure, gamma, alpha.
exists rows; split; [exact Hrows | apply bag_eq_refl].
Qed.

Lemma alpha_gamma_rel_equiv :
  forall bags,
    possible_bag_extensional bags ->
    rel_equiv (alpha (gamma bags)) bags.
Proof.
intros bags Hext bag.
split.
- intros [rows [Hrows Heq]].
  unfold gamma in Hrows.
  exact (proj1 (Hext _ _ Heq) Hrows).
- intro Hbag.
  pose proof (Febag.elements_mk_bag BTupleT bag) as Hrepresentation.
  exists (Febag.elements BTupleT bag).
  split.
  + unfold gamma.
    apply (proj2 (Hext _ _ Hrepresentation)).
    exact Hbag.
  + exact Hrepresentation.
Qed.

Lemma permutation_closure_iff_bag_eq :
  forall observations rows,
    permutation_closure observations rows <->
    exists source,
      observations source /\
      bag_eq (rows_bag source) (rows_bag rows).
Proof.
intros observations rows; reflexivity.
Qed.

Lemma bag_closed_iff_fixed_point :
  forall observations,
    BagClosed observations <->
    rel_equiv (permutation_closure observations) observations.
Proof.
intro observations.
split.
- intros Hclosed rows.
  split.
  + rewrite permutation_closure_iff_bag_eq.
    intros [source [Hsource Heq]].
    exact (proj1 (Hclosed _ _ Heq) Hsource).
  + apply observations_in_permutation_closure.
- intros Hfixed left right Heq.
  split; intro Hrows.
  + apply (proj1 (Hfixed right)).
    rewrite permutation_closure_iff_bag_eq.
    exists left; now split.
  + apply (proj1 (Hfixed left)).
    rewrite permutation_closure_iff_bag_eq.
    exists right; split; [exact Hrows | now apply bag_eq_sym].
Qed.

Lemma gamma_bag_closed :
  forall bags,
    possible_bag_extensional bags ->
    BagClosed (gamma bags).
Proof.
intros bags Hext left right Heq.
unfold gamma.
now apply Hext.
Qed.

Lemma permutation_closure_bag_closed :
  forall observations,
    BagClosed (permutation_closure observations).
Proof.
intro observations.
unfold permutation_closure.
apply gamma_bag_closed.
apply alpha_extensional.
Qed.

Lemma alpha_congr :
  forall left right,
    rel_equiv left right ->
    rel_equiv (alpha left) (alpha right).
Proof.
intros left right Hequiv bag.
unfold alpha.
split; intros [rows [Hrows Heq]]; exists rows; split.
- now apply (proj1 (Hequiv rows)).
- exact Heq.
- now apply (proj2 (Hequiv rows)).
- exact Heq.
Qed.

Theorem bag_closed_rel_equiv_iff_alpha_rel_equiv :
  forall left right,
    BagClosed left ->
    BagClosed right ->
    (rel_equiv left right <-> rel_equiv (alpha left) (alpha right)).
Proof.
intros left right Hleft_closed Hright_closed.
split.
- apply alpha_congr.
- intros Halpha rows.
  split; intro Hrows.
  + assert (Hpossible : alpha left (rows_bag rows)).
    {
      exists rows; split; [exact Hrows | apply bag_eq_refl].
    }
    apply (proj1 (Halpha (rows_bag rows))) in Hpossible.
    destruct Hpossible as [source [Hsource Heq]].
    exact (proj1 (Hright_closed _ _ Heq) Hsource).
  + assert (Hpossible : alpha right (rows_bag rows)).
    {
      exists rows; split; [exact Hrows | apply bag_eq_refl].
    }
    apply (proj2 (Halpha (rows_bag rows))) in Hpossible.
    destruct Hpossible as [source [Hsource Heq]].
    exact (proj1 (Hleft_closed _ _ Heq) Hsource).
Qed.

(** Bag operations are relations so that the abstract layer also supports
    genuinely nondeterministic operators. *)
Definition unary_bag_relation : Type :=
  bagT -> bagT -> Prop.

Definition binary_bag_relation : Type :=
  bagT -> bagT -> bagT -> Prop.

Definition unary_bag_relation_extensional
    (operation : unary_bag_relation) : Prop :=
  forall input_left input_right output_left output_right,
    bag_eq input_left input_right ->
    bag_eq output_left output_right ->
    (operation input_left output_left <->
     operation input_right output_right).

Definition binary_bag_relation_extensional
    (operation : binary_bag_relation) : Prop :=
  forall left_input_left left_input_right
         right_input_left right_input_right
         output_left output_right,
    bag_eq left_input_left left_input_right ->
    bag_eq right_input_left right_input_right ->
    bag_eq output_left output_right ->
    (operation left_input_left right_input_left output_left <->
     operation left_input_right right_input_right output_right).

Definition unary_bag_relation_equiv
    (left right : unary_bag_relation) : Prop :=
  forall input output,
    left input output <-> right input output.

Definition binary_bag_relation_equiv
    (left right : binary_bag_relation) : Prop :=
  forall left_input right_input output,
    left left_input right_input output <->
    right left_input right_input output.

Definition lift_possible_bag_unary
    (operation : unary_bag_relation)
    (inputs : bagT -> Prop) : bagT -> Prop :=
  fun output =>
    exists input,
      inputs input /\
      operation input output.

Definition lift_possible_bag_binary
    (operation : binary_bag_relation)
    (left_inputs right_inputs : bagT -> Prop) : bagT -> Prop :=
  fun output =>
    exists left_input, exists right_input,
      left_inputs left_input /\
      right_inputs right_input /\
      operation left_input right_input output.

Lemma lift_possible_bag_unary_extensional :
  forall operation inputs,
    unary_bag_relation_extensional operation ->
    possible_bag_extensional (lift_possible_bag_unary operation inputs).
Proof.
intros operation inputs Hoperation output_left output_right Heq.
unfold lift_possible_bag_unary.
split; intros [input [Hinput Hresult]]; exists input; split;
  [exact Hinput | | exact Hinput |].
- apply (proj1 (Hoperation input input output_left output_right
    (bag_eq_refl input) Heq)).
  exact Hresult.
- apply (proj2 (Hoperation input input output_left output_right
    (bag_eq_refl input) Heq)).
  exact Hresult.
Qed.

Lemma lift_possible_bag_binary_extensional :
  forall operation left_inputs right_inputs,
    binary_bag_relation_extensional operation ->
    possible_bag_extensional
      (lift_possible_bag_binary operation left_inputs right_inputs).
Proof.
intros operation left_inputs right_inputs Hoperation output_left output_right Heq.
unfold lift_possible_bag_binary.
split;
  intros [left_input [right_input [Hleft [Hright Hresult]]]];
  exists left_input; exists right_input; repeat split;
  try assumption.
- apply (proj1 (Hoperation
    left_input left_input right_input right_input output_left output_right
    (bag_eq_refl left_input) (bag_eq_refl right_input) Heq)).
  exact Hresult.
- apply (proj2 (Hoperation
    left_input left_input right_input right_input output_left output_right
    (bag_eq_refl left_input) (bag_eq_refl right_input) Heq)).
  exact Hresult.
Qed.

Lemma lift_possible_bag_unary_congr :
  forall operation left_inputs right_inputs,
    rel_equiv left_inputs right_inputs ->
    rel_equiv
      (lift_possible_bag_unary operation left_inputs)
      (lift_possible_bag_unary operation right_inputs).
Proof.
intros operation left_inputs right_inputs Hinputs output.
unfold lift_possible_bag_unary.
split; intros [input [Hinput Hresult]]; exists input; split.
- now apply (proj1 (Hinputs input)).
- exact Hresult.
- now apply (proj2 (Hinputs input)).
- exact Hresult.
Qed.

Lemma lift_possible_bag_binary_congr :
  forall operation left_inputs left_inputs'
                   right_inputs right_inputs',
    rel_equiv left_inputs left_inputs' ->
    rel_equiv right_inputs right_inputs' ->
    rel_equiv
      (lift_possible_bag_binary operation left_inputs right_inputs)
      (lift_possible_bag_binary operation left_inputs' right_inputs').
Proof.
intros operation left_inputs left_inputs' right_inputs right_inputs'
  Hleft Hright output.
unfold lift_possible_bag_binary.
split;
  intros [left_input [right_input [Hleft_input [Hright_input Hresult]]]];
  exists left_input; exists right_input; repeat split; try exact Hresult.
- now apply (proj1 (Hleft left_input)).
- now apply (proj1 (Hright right_input)).
- now apply (proj2 (Hleft left_input)).
- now apply (proj2 (Hright right_input)).
Qed.

Lemma lift_possible_bag_unary_operation_congr :
  forall left_operation right_operation inputs,
    unary_bag_relation_equiv left_operation right_operation ->
    rel_equiv
      (lift_possible_bag_unary left_operation inputs)
      (lift_possible_bag_unary right_operation inputs).
Proof.
intros left_operation right_operation inputs Hoperation output.
unfold lift_possible_bag_unary.
split; intros [input [Hinput Hresult]]; exists input; split;
  [exact Hinput | | exact Hinput |].
- now apply (proj1 (Hoperation input output)).
- now apply (proj2 (Hoperation input output)).
Qed.

Lemma lift_possible_bag_binary_operation_congr :
  forall left_operation right_operation left_inputs right_inputs,
    binary_bag_relation_equiv left_operation right_operation ->
    rel_equiv
      (lift_possible_bag_binary left_operation left_inputs right_inputs)
      (lift_possible_bag_binary right_operation left_inputs right_inputs).
Proof.
intros left_operation right_operation left_inputs right_inputs Hoperation output.
unfold lift_possible_bag_binary.
split;
  intros [left_input [right_input [Hleft [Hright Hresult]]]];
  exists left_input; exists right_input; repeat split; try assumption.
- now apply (proj1 (Hoperation left_input right_input output)).
- now apply (proj2 (Hoperation left_input right_input output)).
Qed.

(** The outer SQL outcome is preserved by abstraction.  Only successful list
    observations are quotiented by bag equality; runtime failures remain
    ordinary, explicit outcomes. *)
Definition outcome_alpha
    (observations : sql_outcome (list tuple) -> Prop) :
    sql_outcome bagT -> Prop :=
  fun outcome =>
    match outcome with
    | SqlSuccess bag =>
        alpha (fun rows => observations (SqlSuccess rows)) bag
    | SqlError error => observations (SqlError error)
    end.

Definition OutcomeBagClosed
    (observations : sql_outcome (list tuple) -> Prop) : Prop :=
  BagClosed (fun rows => observations (SqlSuccess rows)).

Lemma outcome_alpha_extensional :
  forall observations,
    possible_bag_extensional
      (fun bag => outcome_alpha observations (SqlSuccess bag)).
Proof.
intro observations.
exact (alpha_extensional (fun rows => observations (SqlSuccess rows))).
Qed.

(** For bag-closed denotations, the possible-bag outcome abstraction is both
    sound and complete for Logos's success-only equivalence contract. *)
Theorem successful_relation_equiv_iff_outcome_alpha :
  forall left right,
    OutcomeBagClosed left ->
    OutcomeBagClosed right ->
    (successful_relation_equiv left right <->
     successful_relation_equiv
         (outcome_alpha left) (outcome_alpha right)).
Proof.
intros left right Hleft_closed Hright_closed.
split.
- intros [[rows Hrows] [Hleft_error [Hright_error Hsuccess]]].
  unfold successful_relation_equiv.
  split.
  + exists (rows_bag rows); simpl.
    exists rows; split; [exact Hrows | apply bag_eq_refl].
  + split.
    * intros error Herror; simpl in Herror.
      exact (Hleft_error error Herror).
    * split.
      -- intros error Herror; simpl in Herror.
         exact (Hright_error error Herror).
      -- intro bag; simpl.
         exact
           (alpha_congr
             (left := fun rows => left (SqlSuccess rows))
             (right := fun rows => right (SqlSuccess rows))
             Hsuccess bag).
- intros [[bag Hbag] [Hleft_error [Hright_error Hsuccess]]].
  unfold successful_relation_equiv.
  simpl in Hbag.
  destruct Hbag as [rows [Hrows _]].
  split; [now exists rows |].
  split.
  + intros error Herror.
    apply (Hleft_error error); exact Herror.
  + split.
    * intros error Herror.
      apply (Hright_error error); exact Herror.
    * apply (proj2
        (bag_closed_rel_equiv_iff_alpha_rel_equiv
          Hleft_closed Hright_closed)).
      intro possible_bag; exact (Hsuccess possible_bag).
Qed.

End Sec.
