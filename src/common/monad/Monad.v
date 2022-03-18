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

Require Import List.

Module Monad.

Record Rcd : Type :=
  mk_R
    { 
      m : Type -> Type;
      return_ (A : Type) (a : A) : m A;
      bind (A B : Type) (x : m A) (f : A -> m B) : m B;
      bind_return_left : forall (A : Type) (a : A) (f : A -> m A), bind (return_ a) f = f a;
      bind_return_right : forall (A : Type) (x : m A), bind x (@return_ _) = x;
      assoc : forall (A B C : Type) (x : m A) (f : A -> m B) (g : B -> m C), 
          bind (bind x f) g = bind x (fun a => bind (f a) g) 
    }.

Definition lift (M : Rcd) (A B : Type) (f : A -> B) (a : m M A) :=
  bind M _ a (fun a => return_ M (f a)).

Fixpoint map (M : Rcd) (A B : Type)  (f : A -> m M B) (l : list A) :=
    match l with
    | nil => return_ M (@nil B)
    | a :: k =>
      bind _ _ (f a) (fun h => bind _ _ (map M B f k) (fun t => return_ M (cons h t)))
    end.

End Monad.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "m >>= f" := (Monad.bind _ _ m f) (at level 42, right associativity) : monad_scope.

Definition MOption : Monad.Rcd.
split with 
    option
    (fun (A : Type) (a : A) => Some a) 
    (fun A B x f => match x with Some a => f a | None => None end).
- intros; apply refl_equal.
- intros A [a | ]; apply refl_equal.
- intros A B C [a | ] f g; apply refl_equal.
Defined.

Definition omap := fun (A B : Type) (f : A -> option B) =>
    fix omap (l : list A) : option (list B) :=
  match l with
  | nil => Some nil
  | a :: l => 
    match f a, omap l with 
    | Some b, Some l' => Some (b :: l') 
    | _, _ => None 
    end
  end.

Lemma map_option_omap :
  forall (A B : Type) (f : A -> option B) (l : list A), Monad.map MOption B f l = omap f l.
Proof.
intros A B f l; induction l as [ | a l]; [apply refl_equal | simpl].
case (f a); [ | apply refl_equal].
intro b; rewrite IHl; apply refl_equal.
Qed.

