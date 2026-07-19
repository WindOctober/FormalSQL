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

From Stdlib Require Import List NArith.
Require Import ListFacts.

Inductive tree (A : Type) : Type :=
  | Leaf : A -> tree A
  | Node : N -> list (tree A) -> tree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint tree_size {A : Type} (value : tree A) : nat :=
  match value with
  | Leaf _ => 1
  | Node _ children => 1 + list_size tree_size children
  end.

Lemma tree_size_unfold :
  forall (A : Type) (value : tree A),
    tree_size value =
      match value with
      | Leaf _ => 1
      | Node _ children => 1 + list_size (@tree_size A) children
      end.
Proof.
intros A [leaf | tag children]; reflexivity.
Qed.
