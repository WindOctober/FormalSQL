(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(**           Possible-bag abstraction of exact ordered observations               *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

From Stdlib Require Import List Sorting.Permutation.

Require Import ListPermut OrderedSet FiniteBag FiniteCollection FlatData SqlOutcome.

(** Ordered row-list outcomes are the single exact evaluator semantics.
    [ordered_rows_equiv] is the SQL observation boundary: it retains order and
    multiplicity while hiding tuple representation details.  [alpha] then
    maps ordered observations to possible bags.  [BagClosed] states exactly
    the recovery property needed to return from a possible bag to an ordered
    SQL observation; it never requires the evaluator to manufacture a chosen
    hidden Rocq tuple representation. *)

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

(** Exact query observations retain list order while comparing each SQL row
    extensionally through [OTuple].  This deliberately ignores only the hidden
    Rocq representation of a tuple; changing row order or multiplicity remains
    observable. *)
Definition ordered_rows_equiv (left right : list tuple) : Prop :=
  Oeset.compare (mk_oelists (OTuple T)) left right = Eq.

Lemma ordered_rows_equiv_refl :
  forall rows, ordered_rows_equiv rows rows.
Proof.
intro rows; unfold ordered_rows_equiv.
apply Oeset.compare_eq_refl.
Qed.

Lemma ordered_rows_equiv_sym :
  forall left right,
    ordered_rows_equiv left right -> ordered_rows_equiv right left.
Proof.
intros left right Hequiv; unfold ordered_rows_equiv in *.
now apply Oeset.compare_eq_sym.
Qed.

Lemma ordered_rows_equiv_trans :
  forall first second third,
    ordered_rows_equiv first second ->
    ordered_rows_equiv second third ->
    ordered_rows_equiv first third.
Proof.
intros first second third Hfirst Hsecond; unfold ordered_rows_equiv in *.
eapply Oeset.compare_eq_trans; eassumption.
Qed.

Lemma ordered_rows_equiv_implies_bag_eq :
  forall left right,
    ordered_rows_equiv left right ->
    bag_eq (rows_bag left) (rows_bag right).
Proof.
intros left right Hequiv.
unfold ordered_rows_equiv, mk_oelists in Hequiv; simpl in Hequiv.
unfold bag_eq, rows_bag.
rewrite Febag.nb_occ_equal; intro row.
rewrite 2 Febag.nb_occ_mk_bag.
now apply Oeset.nb_occ_eq_2.
Qed.

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

(** A relation is bag-closed when every possible result bag can be realized in
    any requested row order, up to the SQL-visible row equality
    [ordered_rows_equiv].  [desired] is an observation request, not a concrete
    evaluator output: the witness [actual] must be produced by the evaluator,
    but its hidden tuple representation need not be identical to [desired]. *)
Definition BagClosed (observations : list tuple -> Prop) : Prop :=
  forall desired,
    alpha observations (rows_bag desired) ->
    exists actual,
      observations actual /\
      ordered_rows_equiv desired actual.

(** Concrete permutation closure is an implementation certificate for
    [BagClosed], not a second observation semantics.  It deliberately talks
    only about reordering the very same Rocq row representatives.  This makes
    it compositional through order-preserving row operators even when their
    callbacks are not setoid morphisms. *)
Definition ConcretePermutationClosed
    (observations : list tuple -> Prop) : Prop :=
  forall source desired,
    Permutation source desired ->
    observations source ->
    observations desired.

(** A semantic bag equality can be aligned by permuting the concrete rows on
    the left.  The aligned list uses no new tuple representatives; only its
    order changes, while it compares positionally equal to the requested
    right-hand list. *)
Lemma bag_eq_rows_has_concrete_alignment :
  forall source desired,
    bag_eq (rows_bag source) (rows_bag desired) ->
    exists actual,
      Permutation source actual /\
      ordered_rows_equiv desired actual.
Proof.
intros source desired Hbags.
assert (Hpermut : Oeset.permut (OTuple T) source desired).
{
  apply Oeset.nb_occ_permut; intro row.
  unfold bag_eq, rows_bag in Hbags.
  rewrite Febag.nb_occ_equal in Hbags.
  specialize (Hbags row).
  now rewrite 2 Febag.nb_occ_mk_bag in Hbags.
}
clear Hbags.
revert source Hpermut.
induction desired as [|desired_row desired IH]; intros source Hpermut.
- pose proof (Oeset.permut_length Hpermut) as Hlength.
  destruct source as [|source_row source]; [|discriminate].
  exists nil; split; [constructor | apply ordered_rows_equiv_refl].
- destruct (_permut_inv_right Hpermut)
    as [source_row [prefix [suffix [Hrow [Hsource Hrest]]]]].
  subst source.
  destruct (IH _ Hrest) as [aligned [Haligned Hordered]].
  exists (source_row :: aligned); split.
  + eapply Permutation_trans.
    * apply Permutation_sym, Permutation_middle.
    * now apply perm_skip.
  + unfold ordered_rows_equiv in *; simpl.
    pose proof (Oeset.compare_eq_sym (OTuple T) source_row desired_row Hrow)
      as Hrow'.
    rewrite Hrow'.
    exact Hordered.
Qed.

Lemma concrete_permutation_closed_implies_bag_closed :
  forall observations,
    ConcretePermutationClosed observations ->
    BagClosed observations.
Proof.
intros observations Hclosed desired [source [Hsource Hbags]].
destruct (bag_eq_rows_has_concrete_alignment source desired Hbags)
  as [actual [Hpermutation Hordered]].
exists actual; split.
- exact (Hclosed source actual Hpermutation Hsource).
- exact Hordered.
Qed.

(** Exact representative transport is a sufficient implementation principle
    for [BagClosed], notably at bag-reset constructors.  It is intentionally
    not exposed as a second closure notion. *)
Lemma bag_closed_of_exact_transport :
  forall observations,
    (forall first second,
      bag_eq (rows_bag first) (rows_bag second) ->
      observations first ->
      observations second) ->
    BagClosed observations.
Proof.
intros observations Htransport desired [source [Hsource Hbags]].
exists desired; split.
- eapply Htransport; [exact Hbags | exact Hsource].
- apply ordered_rows_equiv_refl.
Qed.

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

Lemma gamma_bag_closed :
  forall bags,
    possible_bag_extensional bags ->
    BagClosed (gamma bags).
Proof.
intros bags Hext desired [source [Hsource Hbags]].
exists desired; split.
- unfold gamma in *.
  now apply (proj1 (Hext _ _ Hbags)).
- apply ordered_rows_equiv_refl.
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

(** Functionality here is always modulo semantic bag equality.  These three
    contracts are deliberately independent of any query constructor: they
    describe a possible-bag relation, a unary bag operator, and a binary bag
    operator respectively. *)
Definition possible_bag_functional (bags : bagT -> Prop) : Prop :=
  forall first second,
    bags first -> bags second -> bag_eq first second.

Definition unary_bag_relation_functional
    (operation : unary_bag_relation) : Prop :=
  forall input first second,
    operation input first -> operation input second -> bag_eq first second.

Definition binary_bag_relation_functional
    (operation : binary_bag_relation) : Prop :=
  forall left_input right_input first second,
    operation left_input right_input first ->
    operation left_input right_input second ->
    bag_eq first second.

(** A functional family of possible inputs remains functional after a
    functional extensional unary relation.  Extensionality is essential: the
    two input witnesses need only be bag-equal, not Leibniz-equal. *)
Lemma lift_possible_bag_unary_functional :
  forall operation inputs,
    unary_bag_relation_extensional operation ->
    unary_bag_relation_functional operation ->
    possible_bag_functional inputs ->
    possible_bag_functional (lift_possible_bag_unary operation inputs).
Proof.
intros operation inputs Hext Hoperation Hinputs first second
  [first_input [Hfirst_input Hfirst]]
  [second_input [Hsecond_input Hsecond]].
pose proof
  (Hinputs first_input second_input Hfirst_input Hsecond_input) as Hinput.
apply (Hoperation first_input first second Hfirst).
apply (proj2
  (Hext first_input second_input second second
    Hinput (bag_eq_refl second))).
exact Hsecond.
Qed.

(** Binary lifting uses the same quotient-respecting argument independently
    for both child relations. *)
Lemma lift_possible_bag_binary_functional :
  forall operation left_inputs right_inputs,
    binary_bag_relation_extensional operation ->
    binary_bag_relation_functional operation ->
    possible_bag_functional left_inputs ->
    possible_bag_functional right_inputs ->
    possible_bag_functional
      (lift_possible_bag_binary operation left_inputs right_inputs).
Proof.
intros operation left_inputs right_inputs Hext Hoperation Hleft_inputs
  Hright_inputs first second
  [first_left [first_right [Hfirst_left [Hfirst_right Hfirst]]]]
  [second_left [second_right [Hsecond_left [Hsecond_right Hsecond]]]].
pose proof
  (Hleft_inputs first_left second_left Hfirst_left Hsecond_left) as Hleft.
pose proof
  (Hright_inputs first_right second_right Hfirst_right Hsecond_right) as Hright.
apply (Hoperation first_left first_right first second Hfirst).
apply (proj2
  (Hext first_left second_left first_right second_right second second
    Hleft Hright (bag_eq_refl second))).
exact Hsecond.
Qed.

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
    BagClosed (fun rows => left (SqlSuccess rows)) ->
    BagClosed (fun rows => right (SqlSuccess rows)) ->
    (successful_relation_equiv ordered_rows_equiv left right <->
     successful_relation_equiv bag_eq
         (outcome_alpha left) (outcome_alpha right)).
Proof.
intros left right Hleft_closed Hright_closed.
split.
- intros [[rows Hrows] [Hleft_error [Hright_error [Hforward Hbackward]]]].
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
      -- split.
         ++ intros left_bag [left_rows [Hleft_rows Hleft_bag]].
            destruct (Hforward left_rows Hleft_rows)
              as [right_rows [Hright_rows Hrows_equiv]].
            exists left_bag; split.
            ** simpl. exists right_rows; split; [exact Hright_rows |].
               eapply bag_eq_trans.
               --- exact
                     (bag_eq_sym
                       (ordered_rows_equiv_implies_bag_eq Hrows_equiv)).
               --- exact Hleft_bag.
            ** apply bag_eq_refl.
         ++ intros right_bag [right_rows [Hright_rows Hright_bag]].
            destruct (Hbackward right_rows Hright_rows)
              as [left_rows [Hleft_rows Hrows_equiv]].
            exists right_bag; split.
            ** simpl. exists left_rows; split; [exact Hleft_rows |].
               eapply bag_eq_trans.
               --- exact (ordered_rows_equiv_implies_bag_eq Hrows_equiv).
               --- exact Hright_bag.
            ** apply bag_eq_refl.
- intros [[bag Hbag] [Hleft_error [Hright_error [Hforward Hbackward]]]].
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
    * split.
      -- intros left_rows Hleft_rows.
         assert (Hleft_bag : outcome_alpha left (SqlSuccess (rows_bag left_rows))).
         {
           simpl. exists left_rows; split; [exact Hleft_rows | apply bag_eq_refl].
         }
         destruct (Hforward (rows_bag left_rows) Hleft_bag)
           as [right_bag [[right_rows [Hright_rows Hright_bag]] Hbags]].
         assert (Hrows_bag : bag_eq (rows_bag right_rows) (rows_bag left_rows)).
         {
           eapply bag_eq_trans; [exact Hright_bag |].
           now apply bag_eq_sym.
         }
         destruct (Hright_closed left_rows) as [actual [Hactual Hordered]].
         {
           unfold alpha.
           exists right_rows; now split.
         }
         now exists actual.
      -- intros right_rows Hright_rows.
         assert (Hright_bag : outcome_alpha right (SqlSuccess (rows_bag right_rows))).
         {
           simpl. exists right_rows; split; [exact Hright_rows | apply bag_eq_refl].
         }
         destruct (Hbackward (rows_bag right_rows) Hright_bag)
           as [left_bag [[left_rows [Hleft_rows Hleft_bag]] Hbags]].
         assert (Hrows_bag : bag_eq (rows_bag left_rows) (rows_bag right_rows)).
         {
           eapply bag_eq_trans; [exact Hleft_bag | exact Hbags].
         }
         destruct (Hleft_closed right_rows) as [actual [Hactual Hordered]].
         {
           unfold alpha.
           exists left_rows; now split.
         }
         exists actual; split; [exact Hactual |].
         now apply ordered_rows_equiv_sym.
Qed.

(** The same abstraction is complete for error-preserving equivalence.  Row
    lists are quotiented only by ordered extensional row equality, while SQL
    runtime-error categories remain exact outer observations. *)
Theorem outcome_relation_equiv_iff_outcome_alpha :
  forall left right,
    BagClosed (fun rows => left (SqlSuccess rows)) ->
    BagClosed (fun rows => right (SqlSuccess rows)) ->
    (outcome_relation_equiv ordered_rows_equiv left right <->
     outcome_relation_equiv bag_eq
       (outcome_alpha left) (outcome_alpha right)).
Proof.
intros left right Hleft_closed Hright_closed.
split.
- intros [Hleft_outcome [Hright_outcome [Hforward [Hbackward Herrors]]]].
  apply outcome_relation_equiv_intro.
  + destruct Hleft_outcome as [[left_rows | error] Houtcome].
    * exists (SqlSuccess (rows_bag left_rows)); simpl.
      exists left_rows; split; [exact Houtcome | apply bag_eq_refl].
    * now exists (SqlError error).
  + destruct Hright_outcome as [[right_rows | error] Houtcome].
    * exists (SqlSuccess (rows_bag right_rows)); simpl.
      exists right_rows; split; [exact Houtcome | apply bag_eq_refl].
    * now exists (SqlError error).
  + intros left_bag [left_rows [Hleft_rows Hleft_bag]].
    destruct (Hforward left_rows Hleft_rows)
      as [right_rows [Hright_rows Hrows_equiv]].
    exists left_bag; split.
    * simpl. exists right_rows; split; [exact Hright_rows |].
      eapply bag_eq_trans.
      -- exact
           (bag_eq_sym
             (ordered_rows_equiv_implies_bag_eq Hrows_equiv)).
      -- exact Hleft_bag.
    * apply bag_eq_refl.
  + intros right_bag [right_rows [Hright_rows Hright_bag]].
    destruct (Hbackward right_rows Hright_rows)
      as [left_rows [Hleft_rows Hrows_equiv]].
    exists right_bag; split.
    * simpl. exists left_rows; split; [exact Hleft_rows |].
      eapply bag_eq_trans.
      -- exact (ordered_rows_equiv_implies_bag_eq Hrows_equiv).
      -- exact Hright_bag.
    * apply bag_eq_refl.
  + intro error; simpl; apply Herrors.
- intros [Hleft_outcome [Hright_outcome [Hforward [Hbackward Herrors]]]].
  apply outcome_relation_equiv_intro.
  + destruct Hleft_outcome as [[left_bag | error] Houtcome].
    * simpl in Houtcome.
      destruct Houtcome as [left_rows [Hleft_rows _]].
      now exists (SqlSuccess left_rows).
    * now exists (SqlError error).
  + destruct Hright_outcome as [[right_bag | error] Houtcome].
    * simpl in Houtcome.
      destruct Houtcome as [right_rows [Hright_rows _]].
      now exists (SqlSuccess right_rows).
    * now exists (SqlError error).
  + intros left_rows Hleft_rows.
    assert (Hleft_bag : outcome_alpha left (SqlSuccess (rows_bag left_rows))).
    {
      simpl. exists left_rows; split; [exact Hleft_rows | apply bag_eq_refl].
    }
    destruct (Hforward (rows_bag left_rows) Hleft_bag)
      as [right_bag [[right_rows [Hright_rows Hright_bag]] Hbags]].
    assert (Hrows_bag : bag_eq (rows_bag right_rows) (rows_bag left_rows)).
    {
      eapply bag_eq_trans; [exact Hright_bag |].
      now apply bag_eq_sym.
    }
    destruct (Hright_closed left_rows) as [actual [Hactual Hordered]].
    {
      unfold alpha.
      exists right_rows; now split.
    }
    now exists actual.
  + intros right_rows Hright_rows.
    assert (Hright_bag : outcome_alpha right (SqlSuccess (rows_bag right_rows))).
    {
      simpl. exists right_rows; split; [exact Hright_rows | apply bag_eq_refl].
    }
    destruct (Hbackward (rows_bag right_rows) Hright_bag)
      as [left_bag [[left_rows [Hleft_rows Hleft_bag]] Hbags]].
    assert (Hrows_bag : bag_eq (rows_bag left_rows) (rows_bag right_rows)).
    {
      eapply bag_eq_trans; [exact Hleft_bag | exact Hbags].
    }
    destruct (Hleft_closed right_rows) as [actual [Hactual Hordered]].
    {
      unfold alpha.
      exists left_rows; now split.
    }
    exists actual; split; [exact Hactual |].
    now apply ordered_rows_equiv_sym.
  + intro error; simpl in *; apply Herrors.
Qed.

End Sec.
