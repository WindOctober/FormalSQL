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

(* 
Flata data are tuples.
*)

Module Tuple.

Record Rcd : Type :=
  mk_R
    {
    (** Basic ingredients, predicates, symbols, aggregates, attributes, domains and values *)
    type : Type;
    attribute : Type;
    value : Type;
    predicate : Type;
    symbol : Type;
    aggregate : Type;
    (** Abstract tuples *)
    tuple : Type;
    (** particular values *)
    default_value : type -> value;
    (** comparisons *)
    OAtt : Oset.Rcd attribute;
    A : Fset.Rcd OAtt;
    OVal : Oset.Rcd value;
    FVal : Fset.Rcd OVal;
    OPred : Oset.Rcd predicate;
    OSymb : Oset.Rcd symbol;
    OAgg : Oset.Rcd aggregate;
    OTuple : Oeset.Rcd tuple;
    CTuple : Fecol.Rcd OTuple;
    (** Typing attributes and values. *)
    type_of_attribute : attribute -> type;
    type_of_value : value -> type;
    (** labels and field extraction *)
    labels : tuple -> Fset.set A;
    dot : tuple -> attribute -> value;
    mk_tuple : Fset.set A -> (attribute -> value) -> tuple;
    (** Interpretation *)
    B : Bool.Rcd;
    interp_predicate : predicate -> list value -> Bool.b B;
    interp_symbol : symbol -> list value -> value;
    interp_aggregate : aggregate -> list value -> value;
    (** Properties *)
    labels_mk_tuple : forall s f, labels (mk_tuple s f) =S= s;
    dot_mk_tuple : 
      forall a s f, dot (mk_tuple s f) a =
                    if a inS? s then f a else default_value (type_of_attribute a);
    tuple_eq :
      forall t1 t2, (Oeset.compare OTuple t1 t2 = Eq) <->
                    (labels t1 =S= labels t2 /\ forall a, a inS (labels t1) -> dot t1 a = dot t2 a)
  }.

Section Sec.

Notation "t1 '=t=' t2" := (Oeset.compare (OTuple _) t1 t2 = Eq) 
                            (at level 70, no associativity).
Notation "s1 '=PE=' s2" :=  (Oeset.permut (Tuple.OTuple _) s1 s2) 
                              (at level 70, no associativity).

Hypothesis T : Rcd.

Definition OLTuple : Oeset.Rcd (list (tuple T)) := OLA (OTuple T).

Lemma tuple_eq_labels :
  forall t1 t2, t1 =t= t2 -> labels T t1 =S= labels T t2.
Proof.
intros t1 t2; rewrite tuple_eq; apply proj1.
Qed.

Lemma tuple_eq_dot :
  forall t1 t2, t1 =t= t2 -> 
    forall a, 
      (if a inS? labels T t1 then dot T t1 a else default_value T (type_of_attribute T a)) = 
      (if a inS? labels T t2 then dot T t2 a else default_value T (type_of_attribute T a)).
Proof.
intros t1 t2 H a; rewrite tuple_eq in H.
rewrite <- (Fset.mem_eq_2 _ _ _ (proj1 H)).
case_eq (a inS? labels T t1); intro Ha; [ | apply refl_equal].
apply (proj2 H _ Ha).
Qed.

Lemma tuple_eq_dot_alt :
  forall t1 t2, t1 =t= t2 -> 
     forall a, a inS labels T t1 -> dot T t1 a = dot T t2 a.
Proof.
intros t1 t2 Ht a Ha; rewrite tuple_eq in Ht.
apply (proj2 Ht); apply Ha.
Qed.
           
(*
Specific tuples.
*)

Definition empty_tuple := 
  mk_tuple T (Fset.empty (A T)) (fun a => default_value T (type_of_attribute T a)).

Definition default_tuple s := 
  mk_tuple T s (fun a => default_value T (type_of_attribute T a)).

Lemma labels_empty_tuple : labels T empty_tuple =S= emptysetS.
Proof.
unfold empty_tuple; apply labels_mk_tuple.
Qed.

(*
Building tuples
*)
Lemma mk_tuple_eq_1 :
  forall s1 s2 f, s1 =S= s2 -> mk_tuple T s1 f =t= mk_tuple T s2 f.
Proof.
intros s1 s2 f H; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _ )).
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  assumption.
- intros a Ha.
  rewrite 2 dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ H); apply refl_equal.
Qed.

Lemma mk_tuple_eq_2 :
  forall s f1 f2, (forall a, a inS s -> f1 a = f2 a) -> mk_tuple T s f1 =t= mk_tuple T s f2.
Proof.
intros s f1 f2 H; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)), 
      (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  apply Fset.equal_refl.
- intros a Ha; rewrite 2 dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha; rewrite Ha.
  apply H; assumption.
Qed.

Lemma mk_tuple_eq :
  forall s1 s2 f1 f2, s1 =S= s2 -> (forall a, a inS s1 -> a inS s2 -> f1 a = f2 a) ->
    mk_tuple T s1 f1 =t= mk_tuple T s2 f2.
Proof.
intros s1 s2 f1 f2 Hs Hf.
refine (Oeset.compare_eq_trans _ _ _ _ (mk_tuple_eq_1 _ _ _ Hs) _).
apply mk_tuple_eq_2.
intros a Ha; apply Hf; trivial.
rewrite (Fset.mem_eq_2 _ _ _ Hs); apply Ha.
Qed.

Lemma mk_tuple_idem :
  forall t s, labels T t =S= s -> mk_tuple T s (dot T t) =t= t.
Proof.
intros t s H; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ H).
  apply Fset.equal_refl.
- intros a Ha; rewrite dot_mk_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha; rewrite Ha.
  apply refl_equal.
Qed.

(** Tuples' canonization *)
Definition tuple_as_pairs (t : tuple T) :=
  let labels_t := Fset.elements (A T) (labels T t) in
  List.map (fun a => (a, dot T t a)) labels_t.

Definition pairs_as_tuple t' :=
  let s := Fset.mk_set (A T) (List.map (@fst _ _) t') in 
  mk_tuple T s
    (fun a => 
       match Oset.find (OAtt T) a t' with 
         | Some b => b 
         | None => default_value T (type_of_attribute T a) 
       end).

Definition canonized_tuple t := pairs_as_tuple (tuple_as_pairs t).

Lemma canonized_tuple_eq :
  forall t, (canonized_tuple t) =t= t.
Proof.
intro t. 
unfold canonized_tuple, tuple_as_pairs, pairs_as_tuple.
rewrite map_map; simpl; rewrite map_id; [ | intros; apply refl_equal].
rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  apply Fset.mk_set_idem.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  rewrite dot_mk_tuple, Ha.
  rewrite Oset.find_map; [apply refl_equal | ].
  rewrite Fset.mem_mk_set, <- Fset.mem_elements in Ha.
  apply Fset.mem_in_elements; assumption.
Qed.

Lemma tuple_as_pairs_canonizes :
  forall t1 t2, t1 =t= t2 <-> tuple_as_pairs t1 = tuple_as_pairs t2.
Proof.
intros t1 t2; split; intro H.
- rewrite tuple_eq in H; destruct H as [H1 H2].
  unfold tuple_as_pairs; rewrite <- (Fset.elements_spec1 _ _ _ H1), <- map_eq.
  intros a Ha; apply f_equal; apply H2.
  apply Fset.in_elements_mem; assumption.
- refine (Oeset.compare_eq_trans _ _ _ _ _ (canonized_tuple_eq _)).
  unfold canonized_tuple; rewrite <- H; apply Oeset.compare_eq_sym.
  apply canonized_tuple_eq.
Qed.

(*
Joining tuples
*)

(* Joining tuples *)
(** Test whether t1 and t2 have compatible values on the common attributes. *)
Definition join_compatible_tuple (t1 t2 : tuple T) : bool :=
 Fset.for_all (A T)
   (fun a => 
      match Oset.compare (OVal T) (dot T t1 a) (dot T t2 a) with 
        | Eq => true 
        | Lt | Gt => false 
      end)
   (labels T t1 interS labels T t2).

Definition join_tuple t1 t2 :=
  mk_tuple 
    T (labels T t1 unionS labels T t2) 
    (fun a => if a inS? labels T t1 then dot T t1 a else dot T t2 a).

Lemma join_tuple_unfold : 
  forall t1 t2, join_tuple t1 t2 = 
                mk_tuple 
                  T (labels T t1 unionS labels T t2) 
                  (fun a => if a inS? labels T t1 then dot T t1 a else dot T t2 a).
Proof.
intros t1 t2; apply refl_equal.
Qed.

Lemma join_compatible_tuple_alt :
 forall t1 t2, 
   join_compatible_tuple t1 t2 = true <->
   (forall a, a inS labels T t1 -> a inS labels T t2 -> dot T t1 a = dot T t2 a).
Proof.
intros t1 t2; unfold join_compatible_tuple.
rewrite Fset.for_all_spec, forallb_forall; split.
- intros H a Ha1 Ha2.
  assert (Ha := H a).
  rewrite compare_eq_true, Oset.compare_eq_iff in Ha; apply Ha.
  rewrite Fset.elements_inter; split; 
  rewrite <- (Oset.mem_bool_true_iff (OAtt T)), <- Fset.mem_elements;
  assumption.
- intros H a Ha; rewrite Fset.elements_inter in Ha.
  rewrite compare_eq_true, Oset.compare_eq_iff; 
    apply H; apply Fset.in_elements_mem; [apply (proj1 Ha) | apply (proj2 Ha)].
Qed.

Lemma join_compatible_tuple_eq_1 :
  forall t1 t2 t, t1 =t= t2 ->
    join_compatible_tuple t1 t = join_compatible_tuple t2 t.
Proof.
intros t1 t2 t Ht; rewrite tuple_eq in Ht.
rewrite eq_bool_iff, 2 join_compatible_tuple_alt; split;
intros K a Ha Ka.
- rewrite <- (proj2 Ht); [ | rewrite (Fset.mem_eq_2 _ _ _ (proj1 Ht)); assumption].
  apply K; [rewrite (Fset.mem_eq_2 _ _ _ (proj1 Ht)) | ]; assumption.
- rewrite (proj2 Ht); [ | assumption].
  apply K; [rewrite <- (Fset.mem_eq_2 _ _ _ (proj1 Ht)) | ]; assumption.
Qed. 

Lemma join_compatible_tuple_eq_2 :
  forall t1 t2 t, t1 =t= t2 ->
    join_compatible_tuple t t1 = join_compatible_tuple t t2.
Proof.
intros t1 t2 t Ht; rewrite tuple_eq in Ht. 
rewrite eq_bool_iff, 2 join_compatible_tuple_alt; split;
intros K a Ha Ka.
- rewrite <- (proj2 Ht); [ | rewrite (Fset.mem_eq_2 _ _ _ (proj1 Ht)); assumption].
  apply K; [ | rewrite (Fset.mem_eq_2 _ _ _ (proj1 Ht))]; assumption.
- rewrite (proj2 Ht); [ | assumption].
  apply K; [ | rewrite <- (Fset.mem_eq_2 _ _ _ (proj1 Ht))]; assumption.
Qed. 

Lemma join_compatible_tuple_eq :
  forall t1 t2 t1' t2', 
    t1 =t= t1' -> t2 =t= t2' -> join_compatible_tuple t1 t2 = join_compatible_tuple t1' t2'.
Proof.
intros t1 t2 t1' t2' H H'.
rewrite (join_compatible_tuple_eq_1 _ _ _ H); apply join_compatible_tuple_eq_2; assumption.
Qed.

Lemma join_tuple_eq :
 forall t1 t2 s1 s2, t1 =t= s1 -> t2 =t= s2 -> join_tuple t1 t2 =t= join_tuple s1 s2.
Proof.
intros t1 t2 s1 s2 H1 H2.
rewrite tuple_eq, Fset.equal_spec in H1, H2.
unfold join_tuple; apply mk_tuple_eq.
- rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union, (proj1 H1), (proj1 H2); apply refl_equal.
- intros a Ha Ka; case_eq (a inS? labels T t1); intro Ha1.
  + rewrite <- (proj1 H1), Ha1; apply (proj2 H1); assumption.
  + rewrite (proj1 H1) in Ha1; rewrite Ha1; apply (proj2 H2).
    rewrite Fset.mem_union, Ha1, Bool.Bool.orb_false_l in Ka.
    rewrite (proj1 H2); assumption.
Qed.

Lemma join_tuple_eq_1 :
  forall x1 x1' x2, x1 =t= x1' -> join_tuple x1 x2 =t= join_tuple x1' x2.
Proof.
intros; apply join_tuple_eq; [assumption | apply Oeset.compare_eq_refl].
Qed.

Lemma join_tuple_eq_2 :
  forall x1 x2 x2', x2 =t= x2' -> join_tuple x1 x2 =t= join_tuple x1 x2'.
Proof.
intros; apply join_tuple_eq; [apply Oeset.compare_eq_refl | assumption].
Qed.

Lemma join_tuple_comm : 
  forall t1 t2, join_compatible_tuple t1 t2 = true -> join_tuple t1 t2 =t= join_tuple t2 t1.
Proof.
intros t1 t2 H; rewrite join_compatible_tuple_alt in H.
unfold join_tuple; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _));
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)), Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union; apply Bool.Bool.orb_comm.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  rewrite 2 dot_mk_tuple, Ha.
  case_eq (a inS? labels T t1); intro Ha1.
  + rewrite Fset.mem_union, Ha1, Bool.orb_true_r.
    case_eq (a inS? labels T t2); intro Ha2; [ | apply refl_equal].
    apply (H a Ha1 Ha2).
  + case_eq (a inS? labels T t2); intro Ha2.
    * rewrite Fset.mem_union, Ha1, Ha2; apply refl_equal.
    * rewrite Fset.mem_union, Ha1, Ha2 in Ha.
      discriminate Ha.
Qed.

Lemma join_tuple_assoc : 
  forall t1 t2 t3, join_tuple t1 (join_tuple t2 t3) =t= join_tuple (join_tuple t1 t2) t3.
Proof.
intros t1 t2 t3; unfold join_tuple; rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_2 _ _ _ _ (labels_mk_tuple _ _ _))).
  rewrite (Fset.equal_eq_2 _ _ _ _ (Fset.union_eq_1 _ _ _ _ (labels_mk_tuple _ _ _))).
  apply Fset.union_assoc.
- intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  rewrite !dot_mk_tuple, Ha, !Fset.mem_union.
  rewrite !(Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
  case_eq (a inS? labels T t1); intro Ha1; [simpl; apply refl_equal | simpl].
  case_eq (a inS? labels T t2); intro Ha2; [simpl; apply refl_equal | simpl].
  apply refl_equal.
Qed.

Lemma join_tuple_empty_1 :
  forall t, join_tuple empty_tuple t =t= t.
Proof.
intro t. 
unfold join_tuple, empty_tuple.
rewrite tuple_eq; split_tac.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_1 _ _ _ _ (Fset.union_eq_1 _ _ _ _ (labels_mk_tuple _ _ _))).
  rewrite Fset.equal_spec; intro a.
  rewrite Fset.mem_union, Fset.empty_spec, Bool.Bool.orb_false_l.
  apply refl_equal.
- intros a Ha; rewrite dot_mk_tuple.
  rewrite Fset.mem_union, (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)).
  rewrite Fset.empty_spec, Bool.Bool.orb_false_l.
  rewrite (Fset.mem_eq_2 _ _ _ H) in Ha; rewrite Ha.
  apply refl_equal.
Qed.

Lemma join_tuple_empty_2 :
  forall t, join_tuple t empty_tuple =t= t.
Proof.
intro t; refine (Oeset.compare_eq_trans _ _ _ _ _ (join_tuple_empty_1 _)).
apply join_tuple_comm.
rewrite join_compatible_tuple_alt.
intros a _ Ha; unfold empty_tuple in Ha.
rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.empty_spec in Ha; discriminate Ha.
Qed.

Lemma mk_tuple_dot_join_tuple_1 :
  forall s t1 t2, labels T t1 =S= s -> mk_tuple T s (dot T (join_tuple t1 t2)) =t= t1.
Proof.
intros s t1 t2 Hs.
rewrite tuple_eq; split.
- rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite (Fset.equal_eq_2 _ _ _ _ Hs); apply Fset.equal_refl.
- rewrite Fset.equal_spec in Hs.
  intros a Ha; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Ha.
  rewrite dot_mk_tuple, Ha.
  unfold join_tuple; rewrite dot_mk_tuple, Fset.mem_union.
  rewrite Hs, Ha; apply refl_equal.
Qed.

Lemma mk_tuple_dot_join_tuple_2 :
  forall s2 t1 t2, join_compatible_tuple t1 t2 = true -> 
                   labels T t2 =S= s2 -> mk_tuple T s2 (dot T (join_tuple t1 t2)) =t= t2.
Proof.
intros s2 t1 t2 Hj Hs2.
refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t2 t1 Hs2)).
apply mk_tuple_eq_2.
intros a Ha.
assert (Ht := join_tuple_comm _ _ Hj).
rewrite tuple_eq in Ht; apply (proj2 Ht).
unfold join_tuple.
rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
rewrite (Fset.mem_eq_2 _ _ _ Hs2), Ha, Bool.Bool.orb_true_r.
apply refl_equal.
Qed.

Lemma dot_join_tuple_1 :
  forall t1 t2 a, a inS labels T t1 -> dot T (join_tuple t1 t2) a = dot T t1 a.
Proof.
intros t1 t2 a Ha; unfold join_tuple; rewrite dot_mk_tuple, Fset.mem_union, Ha.
apply refl_equal.
Qed.

Lemma dot_join_tuple_2 :
  forall t1 t2 a, a inS? labels T t1 = false -> a inS labels T t2 ->
                  dot T (join_tuple t1 t2) a = dot T t2 a.
Proof.
intros t1 t2 a Ha Ka; unfold join_tuple; rewrite dot_mk_tuple, Fset.mem_union, Ha, Ka.
apply refl_equal.
Qed.

Lemma split_tuple :
  forall s1 s2 t t1 t2,
    labels T t1 =S= s1 -> labels T t2 =S= s2 -> join_compatible_tuple t1 t2 = true ->
    (t =t= (join_tuple t1 t2) <-> (t1 =t= mk_tuple T s1 (dot T t) /\ 
                                   t2 =t= mk_tuple T s2 (dot T t) /\ 
                                   labels T t =S= (s1 unionS s2))).
Proof.
intros s1 s2 t t1 t2 Hs1 Hs2 Hj; split; [intro H | intros [H1 [H2 H3]]]; [split; [ | split] | ].
- apply Oeset.compare_eq_sym. 
  refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_1 _ t1 t2 Hs1)).
  apply mk_tuple_eq_2; intros.
  rewrite tuple_eq in H; apply (proj2 H).
  rewrite (Fset.mem_eq_2 _ _ _ (proj1 H)); unfold join_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
  rewrite (Fset.mem_eq_2 _ _ _ Hs1), H0; apply refl_equal.
- apply Oeset.compare_eq_sym. 
  refine (Oeset.compare_eq_trans _ _ _ _ _ (mk_tuple_dot_join_tuple_2 _ t1 t2 Hj Hs2)).
  apply mk_tuple_eq_2; intros.
  rewrite tuple_eq in H; apply (proj2 H).
  rewrite (Fset.mem_eq_2 _ _ _ (proj1 H)); unfold join_tuple.
  rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), Fset.mem_union.
  rewrite (Fset.mem_eq_2 _ _ _ Hs2), H0, Bool.Bool.orb_true_r; apply refl_equal.
- rewrite tuple_eq in H; rewrite (Fset.equal_eq_1 _ _ _ _ (proj1 H)).
  unfold join_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
  rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2).
  apply refl_equal.
- rewrite tuple_eq; split.
  + rewrite (Fset.equal_eq_1 _ _ _ _ H3).
    unfold join_tuple; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
    rewrite Fset.equal_spec; intro a.
    rewrite 2 Fset.mem_union, (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2).
    apply refl_equal.
  + assert (H : labels T t =S= labels T (join_tuple t1 t2)).
    {
      rewrite (Fset.equal_eq_1 _ _ _ _ H3), Fset.equal_spec; intro a.
      unfold join_tuple.
      rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)), 2 Fset.mem_union; 
        rewrite (Fset.mem_eq_2 _ _ _ Hs1), (Fset.mem_eq_2 _ _ _ Hs2), <- Fset.mem_union.
      apply refl_equal.
    } 
    intros a Ha.
    unfold join_tuple; rewrite dot_mk_tuple.
    unfold join_tuple in H; rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)) in H.
    rewrite <- (Fset.mem_eq_2 _ _ _ H), Ha.
    rewrite tuple_eq in H1, H2.
    case_eq (a inS? labels T t1); intro Ha1.
    * rewrite (proj2 H1 a Ha1), dot_mk_tuple.
      rewrite <- (Fset.mem_eq_2 _ _ _ Hs1), Ha1; apply refl_equal.
    * rewrite (Fset.mem_eq_2 _ _ _ H), Fset.mem_union, Ha1 in Ha; simpl in Ha.
      rewrite (proj2 H2 a Ha), dot_mk_tuple.
      rewrite <- (Fset.mem_eq_2 _ _ _ Hs2), Ha; apply refl_equal.
Qed.

(* 
Renaming tuples
*)
(** An attribute renaming. No assumptions are made at this point, 
    neither about the compatibility of types, 
    nor about the injectivity. *)

Definition renaming := list (attribute T * attribute T).

Definition apply_renaming rho :=
  fun a => 
    match Oset.find (OAtt T) a rho with
      | Some b => b
      | None => a
    end.

Lemma apply_renaming_att :
  forall ss, all_diff (map fst ss) ->
    forall a b, In (a, b) ss -> apply_renaming ss a = b.
Proof.
intros ss Hf a b H.
unfold apply_renaming; rewrite (Oset.all_diff_fst_find (OAtt T) ss a b Hf H).
apply refl_equal.
Qed. 

Lemma apply_renaming_att_alt :
  forall ss, all_diff (map fst ss) ->
             forall a b, In a (map fst ss) -> apply_renaming ss a = b -> In (a, b) ss.
Proof.
intros ss Hss a b Ha H.
unfold apply_renaming in H.
case_eq (Oset.find (OAtt T) a ss).
- intros b' Hb'; rewrite Hb' in H; subst b'.
  apply (Oset.find_some _ _ _ Hb').
- intro Abs; apply False_rec.
  apply (Oset.find_none_alt _ _ _ Abs); assumption.
Qed.

Lemma apply_renaming_apply_renaming_inv_att :
  forall ss, 
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall b, In b (map snd ss) ->
      apply_renaming ss 
        (apply_renaming (map (fun x => match x with (x1, x2) => (x2, x1) end) ss) b) = b.
Proof.
intros ss Hf Hs b Hb.
rewrite in_map_iff in Hb.
destruct Hb as [[a _b] [_Hb Hb]]; simpl in _Hb; subst _b.
rewrite (apply_renaming_att _ Hf _ b); [apply refl_equal | ].
assert (In_eq : forall x1 x2, In x1 ss -> x1 = x2 -> In x2 ss); [intros; subst; assumption | ].
apply (In_eq _ _ Hb); apply f_equal2; [ | apply refl_equal].
apply sym_eq; apply apply_renaming_att.
- rewrite map_map; apply (all_diff_eq Hs).
  rewrite <- map_eq; intros [a1 b1] _; apply refl_equal.
- rewrite in_map_iff.
  eexists; split; [ | apply Hb]; apply refl_equal.
Qed.

Lemma apply_renaming_inv_apply_renaming_att :
  forall ss, 
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall a, In a (map fst ss) ->
      apply_renaming (map (fun x => match x with (x1, x2) => (x2, x1) end) ss) 
                     (apply_renaming ss a) = a.
Proof.
intros ss Hf Hs a Ha.
rewrite in_map_iff in Ha.
destruct Ha as [[_a b] [_Ha Ha]]; simpl in _Ha; subst _a.
rewrite (apply_renaming_att _ Hf _ _ Ha).
apply apply_renaming_att.
- apply (all_diff_eq Hs).
  rewrite map_map, <- map_eq.
  intros [a1 b1] _; apply refl_equal.
- rewrite in_map_iff; eexists; split; [ | apply Ha]; apply refl_equal.
Qed.

Lemma all_diff_one_to_one_apply_renaming :
  forall ss a1 a2, 
    all_diff (map fst ss) -> all_diff (map snd ss) -> In a1 (map fst ss) -> In a2 (map fst ss) -> 
    apply_renaming ss a1 = apply_renaming ss a2 -> a1 = a2.
Proof.
intros ss a1 a2 Hf Hs Ha1 Ha2; unfold apply_renaming; simpl.
rewrite in_map_iff in Ha1; destruct Ha1 as [[_a1 b] [_Ha1 Ha1]]; simpl in _Ha1; subst _a1.
rewrite (Oset.all_diff_fst_find (OAtt T) ss _ _ Hf Ha1).
rewrite in_map_iff in Ha2; destruct Ha2 as [[_a2 b2] [_Ha2 Ha2]]; simpl in _Ha2; subst _a2.
rewrite (Oset.all_diff_fst_find (OAtt T) ss _ _ Hf Ha2); intro; subst b2.
apply (all_diff_snd _ Hs _ _ _ Ha1 Ha2).
Qed.

Definition rename_tuple rho (t : tuple T) : tuple T :=
  mk_tuple 
    T (Fset.map (A T) (A T) rho (labels T t))
    (fun ra : attribute T =>
       match
         Oset.find (OAtt T) ra
                   (map (fun a : attribute T => (rho a, dot T t a))
                        ({{{labels T t}}})) with
       | Some v => v
       | None => default_value T (type_of_attribute T ra)
       end).

Lemma rename_tuple_eq :
  forall rho t1 t2, t1 =t= t2 -> rename_tuple rho t1 =t= rename_tuple rho t2.
Proof.
intros rho t1 t2 H; rewrite tuple_eq in H; unfold rename_tuple; 
  rewrite tuple_eq;  
  rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _));
  rewrite (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)).
split_tac.
- unfold Fset.map; rewrite Fset.equal_spec; intro a.
  rewrite (Fset.elements_spec1 _ _ _ (proj1 H)); apply refl_equal.
- intros b Hb; rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)) in Hb.
  rewrite 2 dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ H0), Hb.
  rewrite <- (Fset.elements_spec1 _ _ _ (proj1 H)).
  unfold Fset.map in Hb; rewrite Fset.mem_mk_set in Hb.
  rewrite Oset.mem_bool_true_iff, in_map_iff in Hb.
  destruct Hb as [a [Hb Ha]]; subst b.
  assert (Ka : forall a, In a ({{{labels T t1}}}) -> dot T t1 a = dot T t2 a).
  {
    intros a1 Ha1; apply (proj2 H).
    apply Fset.in_elements_mem; assumption.
  }
  clear Ha; set (l1 := {{{labels T t1}}}) in *; clearbody l1.
  induction l1 as [ | a1 l1]; [apply refl_equal | simpl].
  case_eq (Oset.eq_bool (OAtt T) (rho a) (rho a1)); intro Ha1.
  + apply Ka; left; apply refl_equal.
  + apply IHl1; intros; apply Ka; right; assumption.
Qed.

(** One-to-one Hypothesis is needed. 
 Counter-Example : rho : a1 -> a, a2 -> a, t = <a1 = 1; a2 = 2>
 rename_tuple rho t = <a=1> 
 dot T (rename_tuple rho t) (rho a2) = dot <a=1> a = 1 and
 dot T t t a2 = 2
 *)
Lemma rename_tuple_ok :
  forall rho t, 
    labels T (rename_tuple rho t) =S= Fset.map _ (A T) rho (labels T t) /\
    ((forall a1 a2, a1 inS labels T t -> a2 inS labels T t -> rho a1 = rho a2 -> a1 = a2) -> 
     forall a, a inS labels T t -> dot T (rename_tuple rho t) (rho a) = dot T t a).
Proof.
intros rho t; unfold rename_tuple; split.
- apply labels_mk_tuple.
- intros Hrho a Ha; unfold Fset.map.
  rewrite dot_mk_tuple, Fset.mem_mk_set.
  rewrite (Oset.mem_bool_map (OAtt T)),
     (Oset.all_diff_fst_find 
        (OAtt T)
        (map (fun a0 : attribute T => (rho a0, dot T t a0)) ({{{labels T t}}}))
        (rho a) (dot T t a)); [apply refl_equal | | | ].
  + rewrite map_map; apply all_diff_map_inj.
    * intros a1 a2 Ha1 Ha2; apply Hrho; apply Fset.in_elements_mem; assumption.
    * apply Fset.all_diff_elements.
  + rewrite in_map_iff; exists a; split; [apply refl_equal | ].
    apply Fset.mem_in_elements; assumption.
  + rewrite <- Fset.mem_elements; assumption.
Qed.

Lemma rename_tuple_inj :
  forall rho t1 t2, 
    (forall a1 a2, a1 inS labels T t1 -> a2 inS labels T t2 -> rho a1 = rho a2 -> a1 = a2) -> 
    t1 =t= t2 <-> rename_tuple rho t1 =t= rename_tuple rho t2.
Proof.
intros rho t1 t2 Hr; split; [apply rename_tuple_eq | ].
unfold rename_tuple; 
  rewrite 2 tuple_eq, (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)),
   (Fset.equal_eq_2 _ _ _ _ (labels_mk_tuple _ _ _)); intros [H1 H2]; split_tac.
- rewrite Fset.equal_spec; intro a.
  rewrite Fset.equal_spec in H1.
  assert (Ha1 := H1 (rho a)).
  unfold Fset.map in Ha1; rewrite 2 Fset.mem_mk_set in Ha1.
  rewrite 2 Fset.mem_elements, eq_bool_iff; split; intro H.
  + assert (H' : Oset.mem_bool (OAtt T) (rho a) (map rho ({{{labels T t2}}})) = true).
    {
      rewrite <- Ha1, Oset.mem_bool_true_iff, in_map_iff.
      exists a; split; [apply refl_equal | ].
      rewrite <- (Oset.mem_bool_true_iff (OAtt T)); apply H.
    }
    rewrite Oset.mem_bool_true_iff, in_map_iff in H'.
    destruct H' as [a' [H' Ha]].
    replace a with a'; [rewrite Oset.mem_bool_true_iff; assumption | ].
    apply sym_eq; apply Hr.
    * rewrite Fset.mem_elements; assumption.
    * apply Fset.in_elements_mem; assumption.
    * apply sym_eq; assumption.
  + assert (H' : Oset.mem_bool (OAtt T) (rho a) (map rho ({{{labels T t1}}})) = true).
    {
      rewrite Ha1, Oset.mem_bool_true_iff, in_map_iff.
      exists a; split; [apply refl_equal | ].
      rewrite <- (Oset.mem_bool_true_iff (OAtt T)); apply H.
    }
    rewrite Oset.mem_bool_true_iff, in_map_iff in H'.
    destruct H' as [a' [H' Ha]].
    replace a with a'; [rewrite Oset.mem_bool_true_iff; assumption | ].
    apply Hr.
    * apply Fset.in_elements_mem; assumption.
    * rewrite Fset.mem_elements; assumption.
    * assumption.
- intros a Ha. 
  assert (Ha' : rho a inS (Fset.map (A T) (A T) rho (labels T t1))).
  {
    unfold Fset.map. 
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    exists a; split; [apply refl_equal | apply Fset.mem_in_elements; assumption].
  }
  assert (Ha2 : dot T
          (mk_tuple T (Fset.map (A T) (A T) rho (labels T t1))
             (fun ra : attribute T =>
              match
                Oset.find (OAtt T) ra
                  (map (fun a : attribute T => (rho a, dot T t1 a)) ({{{labels T t1}}}))
              with
              | Some v => v
              | None => default_value T (type_of_attribute T ra)
              end)) (rho a) =
        dot T
          (mk_tuple T (Fset.map (A T) (A T) rho (labels T t2))
             (fun ra : attribute T =>
              match
                Oset.find (OAtt T) ra
                  (map (fun a : attribute T => (rho a, dot T t2 a)) ({{{labels T t2}}}))
              with
              | Some v => v
              | None => default_value T (type_of_attribute T ra)
              end)) (rho a)).
  {
    apply (H2 (rho a)).
    rewrite (Fset.mem_eq_2 _ _ _ (labels_mk_tuple _ _ _)); assumption.
  } 
  rewrite 2 dot_mk_tuple, <- (Fset.mem_eq_2 _ _ _ H1), Ha', 
    <- (Fset.elements_spec1 _ _ _ H) in Ha2.
  assert (K1 : Oset.find (OAtt T) (rho a)
                         (map (fun a : attribute T => (rho a, dot T t1 a)) ({{{labels T t1}}})) =
               Some (dot T t1 a)).
  {
    case_eq (Oset.find (OAtt T) (rho a)
                       (map (fun a0 : attribute T => (rho a0, dot T t1 a0)) ({{{labels T t1}}}))).
    - intros v Hv.
      assert (Kv := Oset.find_some _ _ _ Hv).
      rewrite in_map_iff in Kv.
      destruct Kv as [a' [Kv Ka']].
      injection Kv; clear Kv; intros K1 K2; subst v; do 2 apply f_equal.
      apply Hr.
      + apply Fset.in_elements_mem; assumption.
      + rewrite <- (Fset.mem_eq_2 _ _ _ H); assumption.
      + assumption.
    - intros Hv; apply False_rec.
      apply (Oset.find_none _ _ _ Hv (dot T t1 a)).
      rewrite in_map_iff; exists a; split; [apply refl_equal | ].
      apply Fset.mem_in_elements; assumption.
  }
  assert (K2 : Oset.find (OAtt T) (rho a)
                         (map (fun a : attribute T => (rho a, dot T t2 a)) ({{{labels T t1}}})) =
               Some (dot T t2 a)).
  {
    case_eq (Oset.find (OAtt T) (rho a)
                       (map (fun a0 : attribute T => (rho a0, dot T t2 a0)) ({{{labels T t1}}}))).
    - intros v Hv.
      assert (Kv := Oset.find_some _ _ _ Hv).
      rewrite in_map_iff in Kv.
      destruct Kv as [a' [Kv Ka']].
      injection Kv; clear Kv; intros _K1 K2; subst v; do 2 apply f_equal.
      apply Hr.
      + apply Fset.in_elements_mem; assumption.
      + rewrite <- (Fset.mem_eq_2 _ _ _ H); assumption.
      + assumption.
    - intros Hv; apply False_rec.
      apply (Oset.find_none _ _ _ Hv (dot T t2 a)).
      rewrite in_map_iff; exists a; split; [apply refl_equal | ].
      apply Fset.mem_in_elements; assumption.
  }
  rewrite K1, K2 in Ha2; assumption.
Qed.

Lemma labels_rename_tuple_apply_renaming :
  forall ss,
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall t, labels T t =S= Fset.mk_set _ (map fst ss) ->
              labels T (rename_tuple (apply_renaming ss) t) =S= Fset.mk_set _ (map snd ss).
Proof.
intros ss Hf Hs t Ht.
unfold rename_tuple; rewrite (Fset.equal_eq_1 _ _ _ _ (labels_mk_tuple _ _ _)).
unfold Fset.map; rewrite (Fset.elements_spec1 _ _ _ Ht).
rewrite Fset.equal_spec; intro a; rewrite 2 Fset.mem_mk_set, eq_bool_iff; split.
- rewrite !Oset.mem_bool_true_iff, !in_map_iff; intros [b [Ha Hb]].
  assert (Kb := Fset.in_elements_mem _ _ _ Hb); rewrite Fset.mem_mk_set in Kb.
  rewrite Oset.mem_bool_true_iff, in_map_iff in Kb.
  destruct Kb as [[_b _a] [_Kb Kb]]; simpl in _Kb; subst _b.
  rewrite (apply_renaming_att _ Hf _ _ Kb) in Ha; subst _a.
  eexists; split; [ | apply Kb]; apply refl_equal.
- rewrite !Oset.mem_bool_true_iff, !in_map_iff; intros [[b _a] [Ha Hb]].
  simpl in Ha; subst _a.
  exists b; split.
  + apply apply_renaming_att; trivial.
  + apply Fset.mem_in_elements.
    rewrite Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
    eexists; split; [ | apply Hb]; apply refl_equal.
Qed.

Lemma dot_rename_tuple_apply_renaming :
  forall ss,
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall t, labels T t =S= Fset.mk_set _ (map fst ss) ->
              forall a b, In (a, b) ss -> 
                          dot T (rename_tuple (apply_renaming ss) t) b = dot T t a.
Proof.
intros ss Hf Hs t Ht a b H.
rewrite <- (apply_renaming_att _ Hf _ _ H).
refine (proj2 (rename_tuple_ok _ _) _ _ _).
- intros a1 a2 Ha1 Ha2; apply all_diff_one_to_one_apply_renaming; trivial.
  + rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha1.
    assumption.
  + rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_mk_set, Oset.mem_bool_true_iff in Ha2.
    assumption.
- rewrite (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_mk_set, Oset.mem_bool_true_iff, in_map_iff.
  eexists; split; [ | apply H]; apply refl_equal.
Qed.


Lemma apply_renaming_apply_renaming_inv_tuple :
  forall ss, 
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall t, labels T t =S= Fset.mk_set _ (map snd ss) ->
              rename_tuple 
                (apply_renaming ss)
                (rename_tuple 
                   (apply_renaming (map (fun x => match x with (x1, x2) => (x2, x1) end) ss)) t) 
              =t= t.
Proof.
intros ss Hf Hs t Ht.
set (ss' := (map (fun x : attribute T * attribute T => let (x1, x2) := x in (x2, x1)) ss)).
assert (Hss : map fst ss = map snd ss').
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
assert (Hss' : map fst ss' = map snd ss).
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
assert (Ht' : labels T (rename_tuple (apply_renaming ss') t) =S= Fset.mk_set (A T) (map snd ss')).
{
  apply labels_rename_tuple_apply_renaming.
  - rewrite Hss'; assumption.
  - rewrite <- Hss; assumption.
  - rewrite Hss'; assumption.
}
rewrite tuple_eq; split_tac.
- rewrite (Fset.equal_eq_2 _ _ _ _ Ht).
  apply labels_rename_tuple_apply_renaming; trivial.
  rewrite Hss; assumption.
- set (t' := rename_tuple (apply_renaming ss') t) in *.
  intros a Ha.
  rewrite (Fset.mem_eq_2 _ _ _ H), (Fset.mem_eq_2 _ _ _ Ht), Fset.mem_mk_set in Ha.
  rewrite Oset.mem_bool_true_iff, in_map_iff in Ha.
  destruct Ha as [[b _a] [_Ha Ha]]; simpl in _Ha; subst _a.
  rewrite <- Hss in Ht'.
  rewrite (dot_rename_tuple_apply_renaming ss Hf Hs t' Ht' _ _ Ha).
  unfold t'.
  apply dot_rename_tuple_apply_renaming.
  + rewrite Hss'; assumption.
  + rewrite <- Hss; assumption.
  + rewrite Hss'; assumption.
  + unfold ss'; rewrite in_map_iff; eexists; split; [ | apply Ha]; apply refl_equal.
Qed.
         
Lemma apply_renaming_inv_apply_renaming_tuple :
  forall ss, 
    all_diff (map fst ss) -> all_diff (map snd ss) ->
    forall t, labels T t =S= Fset.mk_set _ (map fst ss) ->
              rename_tuple 
                (apply_renaming (map (fun x => match x with (x1, x2) => (x2, x1) end) ss))
                (rename_tuple (apply_renaming ss) t) 
              =t= t.
Proof.
intros ss Hf Hs t Ht.
set (ss' := map (fun x : attribute T * attribute T => let (x1, x2) := x in (x2, x1)) ss) in *.
assert (Hss : map fst ss = map snd ss').
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
assert (Hss' : map fst ss' = map snd ss).
{
  unfold ss'; rewrite map_map, <- map_eq.
  intros [] _; apply refl_equal.
}
rewrite Hss in Ht, Hf.
rewrite <- Hss' in Hs.
assert (Aux := apply_renaming_apply_renaming_inv_tuple ss' Hs Hf t Ht).
rewrite <- (Oeset.compare_eq_2 _ _ _ _ Aux).
apply Oeset.compare_eq_refl_alt.
apply f_equal; apply f_equal2; [ | apply refl_equal].
apply f_equal.
unfold ss'; rewrite map_map, map_id; trivial.
intros [a b] _; apply refl_equal.
Qed.

Lemma nb_occ_map_rename_tuple :
  forall rho t l,
    (forall a1 a2 t2, Oeset.mem_bool (OTuple T) t2 l = true ->
                      a1 inS labels T t -> a2 inS labels T t2 -> rho a1 = rho a2 -> a1 = a2) -> 
    Oeset.nb_occ (OTuple T) (rename_tuple rho t) (map (rename_tuple rho) l) =
    Oeset.nb_occ (OTuple T) t l.
Proof.
intros rho t l H; induction l as [ | t1 l]; [apply refl_equal | ].
rewrite map_unfold, 2 (Oeset.nb_occ_unfold _ _ (_ :: _)); apply f_equal2.
- case_eq (Oeset.compare (OTuple T) t t1); intro H1.
  + assert (H1' := H1); rewrite tuple_eq in H1'.
    rewrite (rename_tuple_inj rho) in H1; [rewrite H1; apply refl_equal | ].
    do 2 intro; apply H; rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
  + case_eq (Oeset.compare (OTuple T) (rename_tuple rho t) (rename_tuple rho t1)); 
      intro H2; trivial.
    rewrite <- (rename_tuple_inj rho) in H2; [rewrite H2 in H1; discriminate H1 | ].
    do 2 intro; apply H; rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
  + case_eq (Oeset.compare (OTuple T) (rename_tuple rho t) (rename_tuple rho t1)); 
      intro H2; trivial.
    rewrite <- (rename_tuple_inj rho) in H2; [rewrite H2 in H1; discriminate H1 | ].
    do 2 intro; apply H; rewrite Oeset.mem_bool_unfold, Oeset.compare_eq_refl; apply refl_equal.
- apply IHl.
  intros a1 a2 t2 Ht2; apply H.
  rewrite Oeset.mem_bool_unfold, Ht2, Bool.orb_true_r; apply refl_equal.
Qed.


End Sec.

End Tuple.

(** Exporting notation for equivalent tuples, finite sets of attributes and finite sets of tuples. *)

Notation "t1 '=t=' t2" := (Oeset.compare (Tuple.OTuple _) t1 t2 = Eq) (at level 70, no associativity).
Notation "s1 '=PE=' s2" := (Oeset.permut (Tuple.OTuple _) s1 s2) (at level 70, no associativity).
