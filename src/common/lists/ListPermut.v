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

Require Import Relations List Arith.

Require Import ListFacts Mem.

(** * Permutation over lists, and finite multisets. *)

Inductive _permut (A B : Type) (R : A -> B -> Prop) : (list A -> list B -> Prop) :=
  | Pnil : _permut R nil nil
  | Pcons : forall a b l l1 l2, R a b -> _permut R l (l1 ++ l2) ->
                   _permut R (a :: l) (l1 ++ b :: l2).

(** * Generalization of Pcons, the second constructor of _permut *)
Lemma _permut_strong :
  forall (A B : Type) (R : A -> B -> Prop) a1 a2 l1 k1 l2 k2, 
    R a1 a2 -> _permut R (l1 ++ k1) (l2 ++ k2) ->
    _permut R (l1 ++ a1 :: k1) (l2 ++ a2 :: k2).
Proof.
intros A B R a1 a2; fix _permut_strong 1.
intro l1; case l1; clear l1; [ | intros u1 l1]; intros k1 l2 k2 a1_R_a2 P.
- apply (@Pcons _ _ R a1 a2 k1 l2 k2); trivial.
- inversion P as [ | b1 b2 l k k' b1_R_b2 Q H17 H18]; clear P; subst.
  destruct (split_list _ _ _ _ H18) as [l [[H1 H2] | [H1 H2]]]; clear H18.
  + subst l2.
    revert H2; case l; clear l.
    * intro H2; simpl in H2; subst k2; rewrite <- ass_app; simpl.
      assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (k ++ a2 :: nil) k' b1_R_b2).
      rewrite <- 2 ass_app in Q'; simpl in Q'.
      apply Q'.
      apply _permut_strong; assumption.
    * intros _b2 l2 H2; simpl in H2.
      injection H2; clear H2; do 2 intro; subst _b2 k'; simpl; rewrite <- ass_app.
      assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) k (l2 ++ a2 :: k2) b1_R_b2).
      rewrite ass_app in Q'.
      apply Q'.
      apply (_permut_strong _ _ _ _ a1_R_a2).
      rewrite <- ass_app; assumption.
  + subst k k2.
    assert (Q' := @Pcons _ _ R u1 b2 (l1 ++ a1 :: k1) (l2 ++ a2 :: l) k' b1_R_b2).
      rewrite <- 2 ass_app in Q'; simpl in Q'.
      apply Q'.
      apply (_permut_strong _ _ _ _ a1_R_a2).
      rewrite ass_app; assumption.
Qed.      

(** * Inclusion of permutation relations *)
Lemma _permut_incl :
  forall (A B : Type) (R R' : A -> B -> Prop) l1 l2,
  (forall a b, R a b -> R' a b) -> _permut R l1 l2 -> _permut R' l1 l2.
Proof.
intros A B R R'.
fix _permut_incl 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 H P.
inversion P; apply Pnil.
inversion P as [ | a b k k1 k2 a_R_b Q]; subst.
apply Pcons.
apply (H _ _ a_R_b).
apply (_permut_incl _ _ H Q).
Qed.

(** * Swapping the lists in _permut *)
Lemma _permut_rel_aux :
forall (A B : Type) (R : A -> B -> Prop) l1 l2,
  _permut R l1 l2 -> _permut (fun b a => R a b) l2 l1.
Proof.
intros A B R.
fix _permut_rel_aux 1.
intro l1; case l1; clear l1.
- intros l2 P.
  inversion P; subst.
  apply Pnil.
- intros a l1 l2 P.
  inversion P; clear P; subst.
  apply (_permut_strong (R := fun b a => R a b) b a l0 l3 nil l1 H1).
  simpl.
  apply _permut_rel_aux; assumption.
Qed.

Lemma _permut_rel :
forall (A B : Type) (R : A -> B -> Prop) l1 l2,
  _permut R l1 l2 <-> _permut (fun b a => R a b) l2 l1.
Proof.
intros A B R l1 l2; split; intro P.
- apply _permut_rel_aux; assumption.
- generalize (_permut_rel_aux P).
  apply _permut_incl.
  exact (fun _ _ h => h).
Qed.

(** * Various inversion lemmata *)
Lemma _permut_inv_right_strong :
  forall (A B : Type) (R : A -> B -> Prop) b l1 l2' l2'',
  _permut R l1 (l2' ++ b :: l2'') -> exists a, exists l1', exists l1'',
   (R a b /\ l1 = l1' ++ a :: l1'' /\ _permut R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R.
fix _permut_inv_right_strong 2.
intros b l1; case l1; clear l1; [ | intros a1 l1]; intros l2' l2'' P.
- revert P; case l2'; clear l2'; [intro P | intros a2' l2' P]; inversion P.
- inversion P as [ | a b' l' l1' k2 a_R_b' Q H K]; subst.
  destruct (split_list _ _ _ _ K) as [l [[H1 H2] | [H1 H2]]]; clear K.
  + destruct l as [ | _b' l].
    * simpl in H2; injection H2; clear H2; do 2 intro.
      rewrite <- app_nil_end in H1.
      subst l2' l2'' b'.
      exists a1; exists nil; exists l1; split; [ | split]; trivial.
    * simpl in H2; injection H2; clear H2; do 2 intro.
      subst l2' k2 _b'.
      rewrite ass_app in Q.
      destruct (_permut_inv_right_strong b _ _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
      exists a; exists (a1 :: k1'); exists k1''; split; [assumption | ].
      split; [rewrite app_comm_cons; apply refl_equal | ].
      rewrite <- ass_app; simpl; apply Pcons; [assumption | ].
      rewrite ass_app; assumption.
  + destruct l as [ | _b l].
    * simpl in H2; injection H2; clear H2; do 2 intro.
      rewrite <- app_nil_end in H1.
      subst l2' l2'' b'.
      exists a1; exists nil; exists l1; split; [ | split]; trivial.
    * simpl in H2; injection H2; clear H2; do 2 intro.
      subst l1' l2'' _b.
      rewrite <- ass_app in Q; simpl in Q.
      destruct (_permut_inv_right_strong b _ _ _ Q) as [a [k1' [k1'' [a_R_b [H Q']]]]]; subst.
      exists a; exists (a1 :: k1'); exists k1''; split; [assumption | ].
      split; [rewrite app_comm_cons; apply refl_equal | ].
      rewrite ass_app; simpl; apply Pcons; [assumption | ].
      rewrite <- ass_app; assumption.
Qed.

Lemma _permut_inv_right :
  forall (A B : Type) (R : A -> B -> Prop) b l1 l2, _permut R l1 (b :: l2) -> 
  exists a, exists l1', exists l1'', (R a b /\ l1 = l1' ++ a :: l1'' /\ _permut R (l1' ++ l1'') l2).
Proof.
intros A B R b l1 l2 P.
apply (_permut_inv_right_strong (R := R) b (l1 := l1) nil l2 P).
Qed.

Lemma _permut_inv_left_strong :
  forall (A B : Type) (R : A -> B -> Prop) a l1' l1'' l2,
  _permut R (l1' ++ a :: l1'') l2 -> exists b, exists l2', exists l2'',
   (R a b /\ l2 = l2' ++ b :: l2'' /\ _permut R (l1' ++ l1'') (l2' ++ l2'')).
Proof.
intros A B R a l1' l1'' l2 P.
rewrite _permut_rel in P.
destruct (_permut_inv_right_strong _ _ _ P) as [b [l2' [l2'' [H1 [H2 H3]]]]].
exists b; exists l2'; exists l2''.
split; [assumption | ].
split; [assumption | ].
rewrite _permut_rel; assumption.
Qed.

(** * Compatibility of _permut *)
(** Permutation is compatible with length and size. *)
Lemma _permut_length :
  forall (A : Type) (R : relation A) l1 l2, _permut R l1 l2 -> length l1 = length l2.
Proof.
intros A R; fix _permut_length 1.
intro l; case l; clear l; [ | intros a l]; intros l' P.
inversion P; apply refl_equal.
inversion P as [ | _a b _l l1 l2 H1 H2]; clear P; subst _a _l l'.
rewrite app_length; simpl; rewrite plus_comm; simpl; rewrite plus_comm.
rewrite <- app_length; rewrite (_permut_length l (l1 ++ l2)); trivial.
Qed.

Lemma _permut_size :
  forall (A B : Type) (R : A -> B -> Prop) size size' l1 l2, 
  (forall a a', In a l1 -> In a' l2 -> R a a' -> size a = size' a') ->
  _permut R l1 l2 -> list_size size l1 = list_size size' l2.
Proof.
intros A B R size size'.
fix _permut_size 1. 
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 E P.
- (* 1/2 *)
  inversion P; apply refl_equal.
- (* 1/1 *)
  inversion P as [ | a b l1' l2' l2'' a_R_b P']; subst.
  rewrite list_size_app; simpl.
  rewrite (E a1 b); trivial.
  + rewrite (_permut_size _ (l2' ++ l2'')); [ | | apply P'].
    * rewrite list_size_app; simpl.
      rewrite plus_comm.
      rewrite <- plus_assoc.
      apply (f_equal (fun n => list_size size' l2' + n)).
      apply plus_comm.
    * intros a a' a_in_la a_in_l'; apply E; trivial.
      right; trivial.
      apply in_app; trivial.
  + left; trivial.
  + apply in_or_app; right; left; trivial.
Qed.

Lemma _permut_map :
  forall (A B A' B': Type) (R : A -> B -> Prop) (R' : A' -> B' -> Prop) f1 f2 l1 l2, 
    (forall a b, In a l1 -> In b l2 -> R a b -> R' (f1 a) (f2 b)) ->
    _permut R l1 l2 -> _permut R' (map f1 l1) (map f2 l2).
Proof.
intros A B A' B' R R' f1 f2.
fix _permut_map 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 Compat P.
(* 1/1 *)
inversion P; apply Pnil.
(* 1/2 *)
inversion P as [ | a' b l1' l2' l2'' a_R_b P' H]; clear P; subst.
rewrite map_app; simpl; apply Pcons.
apply Compat; trivial.
left; trivial.
apply in_or_app; right; left; trivial.
rewrite <- map_app; apply _permut_map; trivial.
intros a b' a_in_l1 b'_in_l2; apply Compat.
right; trivial.
apply in_app; trivial.
Qed.

Lemma _permut_app :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   _permut R l1 l2 -> _permut R l1' l2' -> _permut R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R.
fix _permut_app 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l1' l2 l2' P P'.
inversion P; subst; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; clear P; subst.
simpl; rewrite <- ass_app; simpl; apply Pcons; trivial.
rewrite ass_app; apply _permut_app; trivial.
Qed.

Lemma _permut_swapp :
  forall (A B : Type) (R : A -> B -> Prop) l1 l1' l2 l2',
   _permut R l1 l2 -> _permut R l1' l2' -> _permut R (l1 ++ l1') (l2' ++ l2).
Proof.
intros A B R.
fix _permut_swapp 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l1' l2 l2' P P'.
inversion P; subst; rewrite <- app_nil_end; trivial.
inversion P as [ | a b l1'' l2'' l2''' a_R_b Q]; clear P; subst.
simpl; rewrite ass_app; apply Pcons; trivial.
rewrite <- ass_app; apply _permut_swapp; trivial.
Qed.

Lemma in_permut_in :
   forall (A : Type) l1 l2, _permut (@eq A) l1 l2 -> (forall a, In a l1 <-> In a l2).
Proof. 
assert (H : forall (A : Type) l1 l2, _permut (@eq A) l1 l2 -> forall a, In a l2 -> In a l1).
intros A l1 l2 P a a_in_l2;
destruct (In_split _ _ a_in_l2) as [l2' [l2'' H]]; subst.
destruct (_permut_inv_right_strong (R := @eq A) _ _ _ P)  as [a' [l1' [l1'' [a_eq_a' [H _]]]]]; subst.
apply in_or_app; right; left; trivial.
intros A l1 l2 P a; split; apply H; trivial.
rewrite _permut_rel.
revert P; apply _permut_incl.
exact (fun _ _ h => sym_eq h).
Qed.

(** * Permutation is an equivalence, whenever the underlying relation is *)
Lemma _permut_refl : 
   forall (A : Type) (R : A -> A -> Prop) l,  (forall a, In a l -> R a a) -> _permut R l l.
Proof.
intros A R.
fix _permut_refl 1.
intro l; case l; clear l; [ | intros a l]; intro R_refl.
(* 1/2 *)
apply Pnil.
(* 1/1 *)
apply (@Pcons _ _ R a a l nil l).
apply R_refl; left; apply refl_equal.
simpl; apply (_permut_refl l (fun x h => R_refl x (or_intror _ h))).
Qed.

Lemma _permut_sym :
  forall (A : Type) (R : A -> A -> Prop) l1 l2, 
    (forall a b, In a l1 -> In b l2 -> R a b -> R b a) ->
    _permut R l1 l2 -> _permut R l2 l1.
Proof.
intros A R; fix _permut_sym 1.
intro l1; case l1; clear l1; [ | intros a1 l1]; intros l2 R_sym P.
(* 1/2 *)
inversion P; apply Pnil.
(* 1/1 *)
inversion P as [ | a b l1' l2' l2'' a_R_b Q]; subst.
apply (_permut_strong (R := R) b a1 l2' l2'' (@nil A) l1).
apply R_sym; trivial; [left | apply in_or_app; right; left]; trivial.
simpl; apply _permut_sym; trivial.
intros; apply R_sym; trivial; [right | apply in_app]; trivial.
Qed.

Lemma _permut_trans :
  forall (A : Type) (R : A -> A -> Prop) l1 l2 l3,
   (forall a b c, In a l1 -> In b l2 -> In c l3 -> R a b -> R b c -> R a c) ->
   _permut R l1 l2 -> _permut R l2 l3 -> _permut R l1 l3.
Proof.
intros A R; fix _permut_trans 2.
intros l1 l2; case l2; clear l2; [ | intros a2 l2]; intros l3 R_trans P1 P2.
(* 1/2 *)
inversion P2; exact P1.
(* 1/1 *)
destruct (_permut_inv_right P1) as [a1 [l1' [l1'' [a1_R_a2 [H Q1]]]]]; clear P1; subst l1.
inversion P2 as [ | a2' a3 l2' l3' l3'' a2_R_a3 Q2]; subst.
apply _permut_strong.
apply R_trans with a2; trivial.
apply in_or_app; right; left; apply refl_equal.
left; apply refl_equal.
apply in_or_app; right; left; apply refl_equal.
apply _permut_trans with l2; trivial.
intros a b c; intros; apply R_trans with b; trivial.
apply in_app; trivial.
right; trivial.
apply in_app; trivial.
Qed.

Lemma _permut_rev : 
   forall (A : Type) (R : A -> A -> Prop) l,  (forall a, In a l -> R a a) -> _permut R l (rev l).
Proof.
intros A R.
fix _permut_rev 1.
intro l; case l; clear l; [ | intros a l]; intro R_refl.
- (* 1/2 *)
 apply Pnil.
- (* 1/1 *)
  apply (@Pcons _ _ R a a l (rev l) nil).
  + apply R_refl; left; apply refl_equal.
  + rewrite <- app_nil_end; apply _permut_rev.
    intros; apply R_refl; right; assumption.
Qed.

(** * Removing elements in permutated lists *)

Lemma _permut_cons_inside :
  forall (A B : Type) (R : A -> B -> Prop) a b l l1 l2, 
  (forall a1 b1 a2 b2, In a1 (a :: l) -> In b1 (l1 ++ b :: l2) ->
                   In a2 (a :: l) -> In b2 (l1 ++ b :: l2) ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> _permut R (a :: l) (l1 ++ b :: l2) -> _permut R l (l1 ++ l2).
Proof.
intros A B R a b l l1 l2 trans_R a_R_b P;
destruct (_permut_inv_right_strong (R := R) _ _ _ P) as [a' [l1' [l1'' [a'_R_b [H P']]]]].
destruct l1' as [ | a1' l1']; injection H; clear H; intros; subst; trivial.
inversion P' as [ | a'' b' l' k1' k2' a''_R_b' P'' H17 H18]; subst.
apply _permut_strong; trivial.
apply trans_R with b a1'; trivial.
right; apply in_or_app; right; left; trivial.
apply in_or_app; right; left; trivial.
left; trivial.
apply in_app; rewrite <- H18; apply in_or_app; right; left; trivial.
Qed.

Lemma _permut_add_inside :
   forall (A B : Type) (R : A -> B -> Prop) a b l1 l1' l2 l2', 
  (forall a1 b1 a2 b2, In a1 (l1 ++ a :: l1') -> In b1 (l2 ++ b :: l2') ->
                   In a2 (l1 ++ a :: l1') -> In b2 (l2 ++ b :: l2') ->
                   R a1 b1 -> R a2 b1 -> R a2 b2 -> R a1 b2) ->
  R a b -> _permut R (l1 ++ a :: l1') (l2 ++ b :: l2') -> _permut R (l1 ++ l1') (l2 ++ l2').
Proof.
intros A B R a b l1 l1' l2 l2' trans_R a_R_b P.
destruct (_permut_inv_left_strong (R := R) _ _ _ P) as [b' [k2 [k2' [a_R_b' [H P']]]]].
destruct (split_list _ _ _ _ H) as [l [[H1 H2] | [H1 H2]]]; clear H.
- destruct l as [ | b1 l].
  + simpl in H1; injection H2; clear H2; do 2 intro.
    subst b' k2'.
    rewrite <- app_nil_end in H1; subst k2.
    assumption.
  + simpl in H2; injection H2; clear H2; do 2 intro.
    subst l2' k2 b1.
    rewrite <- ass_app in P'; simpl in P'.
    destruct (_permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
    rewrite H, ass_app.
    apply _permut_strong.
    * {
        apply trans_R with b a; trivial.
        - apply in_app; rewrite H.
          apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; do 2 right.
          apply in_or_app; right; left; apply refl_equal.
      }
    * rewrite <- ass_app; assumption.
- destruct l as [ | b1 l].
  + simpl in H1; injection H2; clear H2; do 2 intro.
    subst b' k2'.
    rewrite <- app_nil_end in H1; subst k2.
    assumption.
  + simpl in H2; injection H2; clear H2; do 2 intro.
    subst l2 k2' b1.
    rewrite ass_app in P'.
    destruct (_permut_inv_right_strong (R := R) _ _ _ P') as [a' [k1' [k1'' [a'_R_b' [H P'']]]]].
    rewrite H, <- ass_app; simpl.
    apply _permut_strong.
    * {
        apply trans_R with b a; trivial.
        - apply in_app; rewrite H.
          apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; right; left; apply refl_equal.
        - apply in_or_app; left.
          apply in_or_app; right; left; apply refl_equal.
      }
    * rewrite ass_app; assumption.
Qed.

Lemma _permut_app1 :
  forall (A : Type) (R : relation A), equivalence _ R ->
  forall l l1 l2, _permut R l1 l2 <-> _permut R (l ++ l1) (l ++ l2).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l]; trivial.
simpl; apply (@Pcons _ _ R u u (l ++ l1) (@nil A) (l ++ l2)); trivial.
apply (equiv_refl _ _ E).
(* <- case *)
induction l as [ | u l]; trivial.
apply IHl.
apply (@_permut_cons_inside A A R u u (l ++ l1) (@nil _) (l ++ l2)); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2.
apply (equiv_trans _ _ E) with b1; trivial.
apply (equiv_trans _ _ E) with a2; trivial.
apply (equiv_sym _ _ E); trivial.
apply (equiv_refl _ _ E).
Qed.

Lemma _permut_app2 :
  forall (A : Type) (R : relation A), equivalence _ R ->
  forall l l1 l2, _permut R l1 l2 <-> _permut R (l1 ++ l) (l2 ++ l).
Proof.
intros A R E l l1 l2; split; intro P.
(* -> case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end; trivial.
apply _permut_strong; trivial.
apply (equiv_refl _ _ E).

(* <- case *)
induction l as [ | u l].
do 2 rewrite <- app_nil_end in P; trivial.
apply IHl.
apply (@_permut_add_inside A A R u u); trivial.
intros a1 b1 a2 b2 _ _ _ _ a1_R_b1 a2_R_b1 a2_R_b2;
apply (equiv_trans _ _ E) with b1; trivial.
apply (equiv_trans _ _ E) with a2; trivial.
apply (equiv_sym _ _ E); trivial.
apply (equiv_refl _ _ E).
Qed.

Lemma all_diff_permut_all_diff :
  forall (A : Type) (R : relation A),
    (forall a1 a2, R a1 a2 -> a1 = a2) ->
    forall l1 l2, all_diff l1  -> _permut R l1 l2 -> all_diff l2.
Proof.
intros A R HR l1 l2 H1 _H2.
assert (H2 := _permut_incl _ HR _H2); clear _H2.
revert l2 H2; induction l1 as [ | a1 l1]; intros l2 H.
- inversion H; subst; trivial.
- rewrite all_diff_unfold in H1.
  inversion H; clear H; subst.
  rewrite <- all_diff_app_iff, (all_diff_unfold (_ :: _)).
  assert (IH := IHl1 (proj2 H1) _ H5).
  repeat split.
  + apply (all_diff_app1 _ _ IH).
  + intros a Ha; apply (proj1 H1).
    rewrite (in_permut_in H5).
    apply in_or_app; right; assumption.
  + apply (all_diff_app2 _ _ IH).
  + intros a H2 H3; simpl in H3; destruct H3 as [H3 | H3].
    * subst a.
      apply (proj1 H1 b); [ | apply refl_equal].
      rewrite (in_permut_in H5).
      apply in_or_app; left; assumption.
    * rewrite <- all_diff_app_iff in IH.
      apply (proj2 (proj2 IH) _ H2 H3).
Qed.

(** * A function to decide wether 2 lists are in relation by _permut *)

Definition _remove_common_bool := fun (A : Type) (equiv_bool : A -> A -> bool) =>
fix _remove_common (l l' : list A) : ((list A) * (list A)) :=
match l with 
| nil => (l, l')
| h :: tl => 
  match remove_bool equiv_bool h l' with
  | Some l'' => _remove_common tl l''
  | None => match _remove_common tl l' with (k, k') => (h :: k, k')  end
  end
end.

Lemma _remove_common_bool_is_sound :
  forall (A : Type) equiv_bool (l1 l2 l1' l2': list A), 
    _remove_common_bool equiv_bool l1 l2 =  (l1',l2') ->
              {ll : list (A * A) | (forall t1 t2, In (t1,t2) ll -> equiv_bool t1 t2 = true) /\
                _permut (@eq A) l1 (l1' ++ (map (fun st => fst st) ll)) /\
                _permut (@eq A) l2 (l2' ++ (map (fun st => snd st) ll)) /\
                (forall t1 t2, In t1 l1' -> In t2 l2' -> equiv_bool t1 t2 = false)}.
Proof.
intros A equiv_bool.
fix _remove_common_bool_is_sound 1.
intros l1 l2 l1' l2'; case l1; clear l1; [ | intros a1 l1]; simpl.
- intro H; injection H; clear H; intros; subst.
  exists nil; split; [intros; contradiction | ].
  split; [apply Pnil | ].
  split.
  + simpl; rewrite <- app_nil_end; apply _permut_refl; intros; apply refl_equal.
  + intros; contradiction.
- case_eq (remove_bool equiv_bool a1 l2).
  + intros k2 H2 H.
    assert (K2 := remove_bool_some_is_sound _ _ _ H2).
    case K2; clear K2.
    intros [[a1' k2'] k2''] [K1 [K2 K3]].
    assert (IH := _remove_common_bool_is_sound _ _ _ _ H).
    case IH; clear IH.
    intros ll [Hll [J1 [J2 J3]]].
    exists ((a1, a1') :: ll); split; [ | split; [ | split]].
    * intros t1 t2 Ht; simpl in Ht.
      destruct Ht as [Ht | Ht]; [injection Ht; clear Ht; intros; subst; assumption | ].
      apply Hll; assumption.
    * rewrite map_unfold; simpl fst.
      apply Pcons; [apply refl_equal | assumption].
    * rewrite map_unfold; simpl snd.
      rewrite K2; apply _permut_strong; [apply refl_equal | ].
      rewrite <- K3; assumption.
    * assumption.
  + intros H2 H.
    assert (K2 := remove_bool_none_is_sound _ _ _ H2).
    case_eq (_remove_common_bool equiv_bool l1 l2).
    intros k k' K; rewrite K in H.
    injection H; clear H; do 2 intro; subst l1' l2'.
    assert (IH := _remove_common_bool_is_sound _ _ _ _ K).
    case IH; clear IH.
    intros ll [Hll [J1 [J2 J3]]].
    exists ll; split; [ | split; [ | split]].
    * assumption.
    * simpl.
      apply (@Pcons _ _ _ a1 a1 l1 nil (k ++ map (fun st : A * A => fst st) ll) (refl_equal _)).
      apply J1.
    * assumption.
    * intros t1 t2 Ht1 Ht2; simpl in Ht1.
      destruct Ht1 as [Ht1 | Ht1]; [ | apply J3; assumption].
      subst t1.
      apply K2.
      rewrite (in_permut_in J2).
      apply in_or_app; left; assumption.
Qed.

Definition _permut_bool := fun (A : Type) (equiv_bool : A -> A -> bool) =>
fix _permut_bool (l1 l2 : list A) : bool :=
match l1 with
| nil =>
  match l2 with
  | nil => true
  | _ => false
  end
| t1 :: k1 =>
    match remove_bool equiv_bool t1 l2 with
   | Some k2 => _permut_bool k1 k2
   | None => false
   end
end.

Lemma _permut_bool_true_is_sound :
  forall (A : Type) (equiv_bool : A -> A -> bool) (l1 l2 : list A),
    _permut_bool equiv_bool l1 l2 = true -> _permut (fun x y => equiv_bool x y = true) l1 l2. 
Proof.
intros A equiv_bool. 
fix _permut_bool_true_is_sound 1.
intro l1; case l1; clear l1.
- intros l2; case l2; clear l2.
  + intros _; simpl; apply Pnil.
  + intros a2 l2 P; discriminate P.
- intros a1 l1 l2.
  simpl.
  case_eq (remove_bool equiv_bool a1 l2).
  + intros k2 Hl2 P.
    case (remove_bool_some_is_sound _ _ _ Hl2).
    intros [[a' k] k'] [K1 [K2 K3]].
    subst l2 k2.
    apply Pcons; [assumption | ].
    apply (_permut_bool_true_is_sound l1 (k ++ k') P).
  + intros _ Abs; discriminate Abs.
Qed.

Lemma _permut_bool_is_sound :
  forall (A : Type) (equiv_bool : A -> A -> bool) (l1 l2 : list A),
    (forall a3 b1 a4 b2 : A, 
       In a3 l1 -> In b1 l2 -> In a4 l1 -> In b2 l2 -> 
       equiv_bool a3 b1 = true -> equiv_bool a4 b1 = true -> equiv_bool a4 b2 = true -> 
       equiv_bool a3 b2 = true) -> 
    match _permut_bool equiv_bool l1 l2 with 
      | true => _permut (fun x y => equiv_bool x y = true) l1 l2 
      | false => ~_permut (fun x y => equiv_bool x y = true) l1 l2 
    end.
Proof.
intros A equiv_bool l1 l2 H.
case_eq (_permut_bool equiv_bool l1 l2); intro P.
- apply (_permut_bool_true_is_sound _ _ _ P).
- revert l1 l2 H P.
  fix _permut_bool_is_sound 1.
  + intro l1; case l1; clear l1.
    * {
        intros l2; case l2; clear l2.
        - intros _ Abs; discriminate Abs.
        - intros a2 l2 _ _ P; inversion P.
      }
    * intros a1 l1 l2 H P Q.
      simpl in P.
      {
        case_eq (remove_bool equiv_bool a1 l2).
        - intros k2 H2; rewrite H2 in P.
          case (remove_bool_some_is_sound _ _ _ H2); clear H2.
          intros [[a1' k2'] k2''] [K1 [K2 K3]].
          subst l2 k2.
          assert (H' : forall a3 b1 a4 b2 : A,
                     In a3 l1 ->
                     In b1 (k2' ++ k2'') ->
                     In a4 l1 ->
                     In b2 (k2' ++ k2'') ->
                     equiv_bool a3 b1 = true ->
                     equiv_bool a4 b1 = true ->
                     equiv_bool a4 b2 = true -> equiv_bool a3 b2 = true).
          {
            do 8 intro; apply H.
            - right; assumption.
            - apply in_app; assumption.
            - right; assumption.
            - apply in_app; assumption.
          }
          apply (_permut_bool_is_sound _ _ H' P).
          apply _permut_cons_inside with a1 a1'; trivial.
        - intro H2.
          inversion Q; clear Q; subst.
          assert (Aux : In b (l0 ++ b :: l3)).
          {
            apply in_or_app; right; left; apply refl_equal.
          } 
          assert (Abs := remove_bool_none_is_sound _ _ _ H2 b Aux).
          rewrite H3 in Abs; discriminate Abs.
      }
Qed.          

Lemma permut_filter_eq :
  forall (A : Type) (R : relation A) (f1 f2 : A -> bool) (l1 l2 : list A),
    (forall x1 x2, In x1 l1 -> R x1 x2 -> f1 x1 = f2 x2) ->
    _permut R l1 l2 -> _permut R (filter f1 l1) (filter f2 l2).
Proof.
intros A R f1 f2 l1; induction l1 as [ | x1 l1]; intros l2 H P.
- inversion P; apply Pnil.
- inversion P; subst; rewrite filter_app; simpl.
  assert (Hx1 := H x1 b (or_introl _ (refl_equal _)) H2); rewrite <- Hx1.
  destruct (f1 x1).
  + apply Pcons; [assumption | ].
    rewrite <- filter_app.
    apply IHl1.
    * intros y1 y2 Hy; apply H; right; assumption.
    * assumption.
  + rewrite <- filter_app.
    apply IHl1.
    * intros y1 y2 Hy; apply H; right; assumption.
    * assumption.
Qed.
  
Section PermutiSi.

Hypothesis A : Type.
Hypothesis R : A -> A -> Prop.
Hypothesis ER : equivalence _ R.

Inductive _permut_i_Si : (list A -> list A -> Prop) :=
  | PiSi : forall l1 a1 a2 b1 b2 l2, 
      R a1 a2 -> R b1 b2 -> _permut_i_Si (l1 ++ a1 :: b1 :: l2) (l1 ++ b2 :: a2 :: l2).

Inductive permut_i_Si : (list A -> list A -> Prop) :=
  | ReflStep : forall l1 l2, Forall2 R l1 l2 -> permut_i_Si l1 l2
  | SwappStep : forall l1 l2, _permut_i_Si l1 l2 -> permut_i_Si l1 l2
  | TransStep : forall l1 l2 l3, permut_i_Si l1 l2 -> permut_i_Si l2 l3 -> permut_i_Si l1 l3.

Lemma _permut_i_Si_permut :
  forall l1 l2, _permut_i_Si l1 l2 -> _permut R l1 l2.
Proof.
intros k1 k2 H.
inversion H; subst.
apply _permut_app1; [assumption | ].
apply (Pcons (R := R) a1 a2 (l := b1 :: l2) (b2 :: nil) l2).
- assumption.
- apply (Pcons (R := R) b1 b2 (l := l2) nil l2).
  + assumption.
  + apply _permut_refl; intros; destruct ER; apply equiv_refl.
Qed.

Lemma permut_i_Si_strong :
  forall l1 l1' a1 a2 b1 b2 l2 l2',
    Forall2 R l1 l1' -> R a1 a2 -> R b1 b2 -> Forall2 R l2 l2' ->
    permut_i_Si (l1 ++ a1 :: b1 :: l2) (l1' ++ b2 :: a2 :: l2').
Proof.
destruct ER.
intros l1 l1' a1 a2 b1 b2 l2 l2' H1 Ha Hb H2.
constructor 3 with (l1 ++ a1 :: b1 :: l2').
- constructor 1; clear H1.
  revert l2 l2' H2; induction l1 as [ | x1 l1]; intros l2 l2' H2.
    * simpl; repeat (constructor 2; trivial).
    * simpl; constructor 2; trivial.
      apply IHl1; trivial.
- constructor 3 with (l1' ++ a1 :: b1 :: l2').
  + constructor 1; clear H2.
    revert l1' l2' H1; induction l1 as [ | x1 l1]; intros [ | y1 l1'] l2' H1.
    * simpl; repeat (constructor 2; trivial).
      induction l2' as [ | y2 l2']; simpl; [constructor 1 | ].
      constructor 2; trivial.
    * inversion H1.
    * inversion H1.
    * inversion H1; subst; simpl; constructor 2; trivial.
      apply IHl1; trivial.
  + constructor 2.
    apply PiSi; trivial.
Qed.

Lemma permut_i_Si_cons :
  forall a1 a2 l1 l2, R a1 a2 -> permut_i_Si l1 l2 -> permut_i_Si (a1 :: l1) (a2 :: l2).
Proof.
destruct ER.
intros c1 c2 l1 l2 Hc Hl; revert c1 c2 Hc; induction Hl; intros c1 c2 Hc.
- constructor 1; constructor 2; assumption.
- inversion H as [k a1 a2 b1 b2 k']; subst.
  rewrite 2 app_comm_cons; apply permut_i_Si_strong; trivial.
  + constructor 2; trivial.
    clear H; induction k as [ | x k]; [constructor 1 | constructor 2; trivial].
  + clear H; induction k' as [ | x k']; [constructor 1 | constructor 2; trivial].
- constructor 3 with (c1 :: l2); [ | apply IHHl2; trivial].
  apply IHHl1; trivial.
Qed.

Lemma permut_i_Si_permut :
  forall l1 l2, permut_i_Si l1 l2 <-> _permut R l1 l2.
Proof.
destruct ER.
intros l1 l2; split; intro H.
- induction H.
  + revert l2 H; induction l1 as [ | a1 l1]; intros [ | a2 l2] H.
    * apply _permut_refl; intros a Ha; contradiction Ha.
    * inversion H.
    * inversion H.
    * inversion H; subst.
      apply (Pcons (R := R) a1 a2 (l := l1) nil l2); [assumption | ].
      apply IHl1; assumption.
  + apply _permut_i_Si_permut; assumption.
  + apply _permut_trans with l2; trivial.
    do 6 intro; apply equiv_trans.
- induction H.
  + constructor 1; constructor 1.
  + constructor 3 with (a :: (l1 ++ l2)); [apply permut_i_Si_cons; trivial | ].
    clear H0 IH_permut.
    revert l2; induction l1 as [ | a1 l1]; intro l2; simpl.
    * constructor 1; constructor 2; trivial.
      induction l2 as [ | a2 l2]; [constructor 1 | constructor 2; trivial].
    * {
        constructor 3 with (a1 :: a :: l1 ++ l2).
        - constructor 2; apply (@PiSi nil); trivial.
        - apply permut_i_Si_cons; trivial.
      }
Qed.

End PermutiSi.

Lemma all_diff_permut :
  forall (A : Type) l1 l2, _permut (@eq A) l1 l2 -> all_diff l1 -> all_diff l2.
Proof.
intros A l1; induction l1 as [ | a1 l1]; intros l2 H; inversion H; clear H; subst.
- exact (fun h => h).
- rewrite all_diff_unfold; intros [H1 H2].
  assert (IH := IHl1 _ H4 H2);   rewrite <- all_diff_app_iff in IH.
  rewrite <- all_diff_app_iff, (all_diff_unfold (_ :: _)).
  split; [apply (proj1 IH) | ].
  split; [split; [ | apply (proj1 (proj2 IH)) ] | ].
  + intros a Ha; apply H1.
    apply (in_permut_in H4); apply in_or_app; right; assumption.
  + intros a Ha H.
    simpl in H; destruct H as [H | H].
    * subst a.
      apply (H1 b); [ | apply refl_equal].
      apply (in_permut_in H4); apply in_or_app; left; assumption.
    * apply (proj2 (proj2 IH) _ Ha H).
Qed.

Lemma partition_spec3_strong :
  forall (A : Type) (f : A -> bool) l l1 l2, partition f l = (l1, l2) -> _permut (@eq A) l (l1 ++ l2).
Proof.
intros A f l; induction l as [ | a1 l]; intros l1 l2 Hl; simpl in Hl.
- injection Hl; clear Hl; do 2 intro; subst l1 l2; apply _permut_refl; intros; apply refl_equal.
- case_eq (partition f l); intros k1 k2 Kl; rewrite Kl in Hl.
  case_eq (f a1); intro Ha1; rewrite Ha1 in Hl; injection Hl; clear Hl; do 2 intro; subst l1 l2.
  + simpl; apply (Pcons a1 a1 nil (k1 ++ k2)); [apply refl_equal | ].
    simpl; apply IHl; apply Kl.
  + apply Pcons; [apply refl_equal | ].
    apply IHl; apply Kl.
Qed.


Definition cartesian_product (A B C : Type) (f : A -> B -> C) l1 l2 :=
  flat_map (fun e1 => map (fun e2 => f e1 e2) l2) l1.

Lemma cartesian_product_app_1 : 
  forall (A B C : Type) (f : A -> B -> C) l1 l1' l2,
    cartesian_product f (l1 ++ l1') l2 = cartesian_product f l1 l2 ++ cartesian_product f l1' l2.
Proof.
intros A B C f l1; induction l1 as [ | a1 l1]; intros l1' l2; simpl; trivial.
- rewrite <-ass_app; apply f_equal.
  apply IHl1.
Qed.

Lemma cartesian_product_app_2 : 
  forall (A B C : Type) (f : A -> B -> C) l1 l2 l2',
    _permut eq (cartesian_product f l1 (l2 ++ l2')) (cartesian_product f l1 l2 ++ cartesian_product f l1 l2').
Proof.
intros A B C f l1; induction l1 as [ | a1 l1]; intros l2 l2'; simpl.
- constructor 1.
- apply _permut_trans with (map (fun e2 : B => f a1 e2) (l2 ++ l2') ++ 
                             (cartesian_product f l1 l2 ++ cartesian_product f l1 l2')).
  + intros; subst; trivial.
  + apply _permut_app1; [ | apply IHl1].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
  + rewrite map_app, <- 2 ass_app; apply _permut_app1.
    * split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
    * rewrite 2 ass_app; apply _permut_app2; 
        [ | apply _permut_swapp; apply _permut_refl; intros; subst; trivial].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
Qed.

Lemma permut_flat_map :
    forall (A B C : Type) (f : A -> B -> C) (lb1 : list (list A)) (lb2 : list (list B)),
      _permut eq (cartesian_product f (flat_map (fun x => x) lb1) (flat_map (fun x => x) lb2)) 
             (flat_map (fun x => x) (cartesian_product (cartesian_product f) lb1 lb2)).
Proof.
intros A B C f lb1; induction lb1 as [ | b1 lb1]; intros lb2; simpl.
- constructor 1.
- rewrite cartesian_product_app_1, flat_map_app.
  apply _permut_app; [ | apply IHlb1].
  clear lb1 IHlb1.
  revert b1; induction lb2 as [ | b2 lb2]; simpl.
  + intro b1; induction b1 as [ | x1 b1]; simpl.
    * constructor 1.
    * assumption.
  + intro b1; simpl.
    apply _permut_trans with
        (cartesian_product f b1 b2 ++
          (cartesian_product f b1 (flat_map (fun x : list B => x) lb2))).
    * intros; subst; trivial.
    * apply cartesian_product_app_2.
    * apply _permut_app1; [ | apply IHlb2].
    split; [unfold reflexive | unfold transitive | unfold symmetric ]; intros; subst; trivial.
Qed.



