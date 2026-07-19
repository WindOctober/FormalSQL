(************************************************************************************)
(**                                                                                 *)
(**                          The SQLFormalSemantics Library                         *)
(**                                                                                 *)
(************************************************************************************)

Require Import List Bool.
Require Import BasicFacts ListPermut OrderedSet.

(** Lightweight equality support for syntax carriers that are never ordered by
    the SQL semantics. *)
Module EqDec.

Definition t (A : Type) := forall left right : A, {left = right} + {left <> right}.

Definition of_oset {A : Type} (ordered : Oset.Rcd A) : t A.
Proof.
intros left right.
generalize (Oset.eq_bool_ok ordered left right).
destruct (Oset.compare ordered left right); intro result.
- left; exact result.
- right; exact result.
- right; exact result.
Defined.

Definition mem {A : Type} (equal : t A) (element : A) (elements : list A) : bool :=
  if in_dec equal element elements then true else false.

Lemma mem_true_iff :
  forall (A : Type) (equal : t A) element elements,
    mem equal element elements = true <-> In element elements.
Proof.
intros A equal element elements; unfold mem.
destruct (in_dec equal element elements) as [Hin | Hnotin].
- split; [exact (fun _ => Hin) | exact (fun _ => refl_equal true)].
- split; [discriminate | exact (fun Hin => False_rec _ (Hnotin Hin))].
Qed.

Lemma mem_app :
  forall (A : Type) (equal : t A) element left right,
    mem equal element (left ++ right) =
      orb (mem equal element left) (mem equal element right).
Proof.
intros A equal element left right.
rewrite eq_bool_iff, Bool.orb_true_iff, !mem_true_iff, in_app_iff.
tauto.
Qed.

Lemma mem_permut :
  forall (A : Type) (equal : t A) element left right,
    _permut (@eq A) left right ->
    mem equal element left = mem equal element right.
Proof.
intros A equal element left right Hpermut.
rewrite eq_bool_iff, !mem_true_iff.
pose proof (in_permut_in Hpermut element).
tauto.
Qed.

End EqDec.
