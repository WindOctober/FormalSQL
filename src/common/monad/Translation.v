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

Inductive translation  (A : Type) : Type :=
  | EndComputation
  | NoTranslation
  | Translation : forall a : A, translation A.
Arguments EndComputation {A}.
Arguments NoTranslation {A}.

Definition monad_apply1 (A B : Type) (f1 : A -> B) m1 :=
  match m1 with
    | Translation a1 => Translation (f1 a1)
    | NoTranslation => @NoTranslation B
    | EndComputation => @EndComputation B
  end.

Definition monad_apply2 (A1 A2 B : Type) (f2 : A1 -> A2 -> B) m1 m2 :=
  match m1, m2 with
    | Translation a1, Translation a2 => Translation (f2 a1 a2)
    | NoTranslation, _
    | _, NoTranslation => @NoTranslation B
    | _, _ => @EndComputation B
  end.

Definition monad_fold_left (A B : Type) (f : A -> B -> A) l acc :=
  List.fold_left
    (fun acc x =>
       match acc, x with
         | Translation acc, Translation x => 
           Translation (f acc x)
         | NoTranslation, _
         | _, NoTranslation => @NoTranslation A
         | _, _ => @EndComputation A
       end)
    l acc.

Fixpoint monad_map (A B : Type) (f : A -> translation B) l :=
  match l with
    | nil => Translation nil
    | a :: k => 
      match f a, monad_map f k with
          | Translation fa, Translation fk => Translation (fa :: fk)
          | NoTranslation, _
          | _, NoTranslation => @NoTranslation _
          | _, _ => @EndComputation _
      end
  end.

Lemma monad_map_unfold : 
 forall (A B : Type) (f : A -> translation B) l, 
 monad_map f l =
  match l with
    | nil => Translation nil
    | a :: k => 
      match f a, monad_map f k with
          | Translation fa, Translation fk => Translation (fa :: fk)
          | NoTranslation, _
          | _, NoTranslation => @NoTranslation _
          | _, _ => @EndComputation _
      end
  end.
Proof.
intros A B f l; destruct l; apply refl_equal.
Qed.

Lemma monad_fold_left_translation :
  forall (A B : Type) (f : A -> B -> A) l acc res,
    monad_fold_left f l acc = Translation res ->
         match acc with
           | Translation _ => True
           | _ => False
         end.
Proof.
intros A B f l; induction l as [ | x l]; intros acc res H; simpl in H.
- subst acc; trivial.
- destruct acc as [ | | y].
  + destruct x as [ | | x].
    * apply (IHl _ _ H).
    * apply (IHl _ _ H).
    * apply (IHl _ _ H).
  + apply (IHl _ _ H).
  + trivial.
Qed.

Lemma in_monad_map_false :
  forall (A B : Type) (f : A -> translation B) (l : list A) res,
    monad_map f l = Translation res -> forall (a : A), 
    List.In a l ->  
    match f a with
      | Translation _ => True
      | _ => False
    end.
Proof.
intros A B f; induction l as [ | a1 l]; intros res H1 a H2.  
- contradiction H2.
- simpl in H2; destruct H2 as [H2 | H2].
  + subst a1; simpl in H1.
    destruct (f a).
    * destruct (monad_map f l); discriminate H1.
    * destruct (monad_map f l); discriminate H1.
    * trivial.
  + simpl in H1; destruct (f a1) as [ | | fa1].
    * destruct (monad_map f l); discriminate H1.
    * destruct (monad_map f l); discriminate H1.
    * case_eq (monad_map f l); [intro K | intro K | intros k K]; 
      rewrite K in H1; try discriminate H1.
      destruct res as [ | x' res']; [discriminate H1 | ].
      injection H1; clear H1; do 2 intro; subst x' res'.
      apply (IHl k K a H2).
Qed.

Lemma in_monad_map_iff :
  forall (A B : Type) f (l : list A) res,
    monad_map f l = Translation res -> 
    forall (b : B), (List.In b res <-> (exists a, List.In a l /\ f a = Translation b)).
Proof.
intros A B f l; induction l as [ | a1 l]; intros res H b.
- simpl in H; injection H; clear H; intro H.
  subst res.
  split; intro K.
  + contradiction K.
  + destruct K as [a [K _]]; contradiction K.
- simpl in H.
  case_eq (f a1).
  + intro K; rewrite K in H.
    destruct (monad_map f l); discriminate H.
  + intro K; rewrite K in H; discriminate H.
  + intros b1 K; rewrite K in H.
    case_eq (monad_map f l).
    * intro J; rewrite J in H; discriminate H.
    * intro J; rewrite J in H; discriminate H.
    * intros k J; rewrite J in H.
      injection H; clear H; intro H; subst res.
      simpl.
      {
        rewrite (IHl _ J); split; intro H.
        - destruct H as [H | [a [Ha Ka]]].
          + subst b1.
            exists a1; split; [left | ]; trivial.
          + exists a; split; [right | ]; trivial.
        - destruct H as [a [[Ha | Ha] Ka]].
          + subst a1.
            rewrite K in Ka; injection Ka; clear Ka; intro; subst b1.
            left; apply refl_equal.
          + right; exists a; split; assumption.
      }
Qed.

Lemma monad_map_map_eq :
  forall (A B C : Type) (f1 : A -> translation B) (f2 : A -> C) (f3 : B -> C) l l',
    (forall a1 fa1, List.In a1 l -> f1 a1 = Translation fa1 -> f2 a1 = f3 fa1) ->
    monad_map f1 l = Translation l' -> map f2 l = map f3 l'.
Proof.
intros A B C f1 f2 f3 l.
induction l as [ | a1 l]; intros [ | b1 l'] Hf H.
- apply refl_equal.
- discriminate H.
- simpl in H.
  destruct (f1 a1).
  + destruct (monad_map f1 l); discriminate H.
  + discriminate H.
  + destruct (monad_map f1 l); discriminate H.
- simpl in H; case_eq (f1 a1).
  + intro H1; rewrite H1 in H; destruct (monad_map f1 l); discriminate H.
  + intro H1; rewrite H1 in H; discriminate H.
  + intros fa1 H1; rewrite H1 in H.
    case_eq (monad_map f1 l).
    * intro Hl1; rewrite Hl1 in H; discriminate H.
    * intro Hl1; rewrite Hl1 in H; discriminate H.
    * intros fl1 Hl1; rewrite Hl1 in H.
      injection H; clear H; intros Hl H.
      subst b1 l'.
      {
        simpl; apply f_equal2.
        - apply Hf.
          + left; apply refl_equal.
          + assumption.
        - apply IHl.
          + do 3 intro; apply Hf; right; assumption.
          + assumption.
      } 
Qed.

