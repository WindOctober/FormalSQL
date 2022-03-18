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

Require Import Arith NArith ZArith String List. 
Require Import ListFacts OrderedSet FiniteSet FiniteBag FiniteCollection FlatData.

Module Tuple1.

Section Sec.

Hypothesis attribute : Type.
Hypothesis type : Type. 
Hypothesis value : Type.
Hypothesis type_of_attribute : attribute -> type. 
Hypothesis type_of_value : value -> type.
Hypothesis default_value : type -> value. 
Hypothesis OAtt : Oset.Rcd attribute. 
Hypothesis FAN : Fset.Rcd OAtt.
Hypothesis OT : Oset.Rcd type.
Hypothesis OVal : Oset.Rcd value.
Hypothesis FVal : Fset.Rcd OVal.

Definition tuple := ((Fset.set FAN) * (attribute -> value))%type.

Definition support := fun (t : tuple) => fst t.

Definition dot := fun (t : tuple) a => match t with (_,f) => f a end.

Definition mk_tuple (fa : Fset.set FAN) (f : attribute -> value) : tuple := 
  (fa, fun a => if a inS? fa then f a else default_value (type_of_attribute a)).

Lemma support_mk_tuple_ok : forall fa f, support (mk_tuple fa f) =S= fa.
Proof.
intros fa f; unfold mk_tuple; simpl; rewrite Fset.equal_spec; intros; apply refl_equal.
Qed.

Lemma dot_mk_tuple_ok : 
  forall a s f, 
    dot (mk_tuple s f) a = (if a inS? s then f a else default_value (type_of_attribute a)).
Proof.
intros a fa f; unfold mk_tuple; simpl; apply refl_equal.
Qed.

Definition tuple_compare (t1 t2 : tuple) : comparison :=
  match t1, t2 with
      | (fa1, f1), (fa2, f2) =>
        compareAB (Fset.compare FAN) (comparelA (Oset.compare OVal)) (fa1, map f1 (Fset.elements FAN fa1)) (fa2, map f2 (Fset.elements FAN fa2))
end.

Definition OTuple : Oeset.Rcd tuple.
Proof.
split with tuple_compare; unfold tuple, tuple_compare.
- (* 1/5 *)
  intros [fa1 t1] [fa2 t2] [fa3 t3].
  apply compareAB_eq_trans.
  + apply Fset.compare_eq_trans.
  + apply comparelA_eq_trans.
    do 6 intro; apply Oset.compare_eq_trans.
- (* 1/4 *)
  intros [fa1 t1] [fa2 t2] [fa3 t3].
  apply compareAB_le_lt_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_eq_lt_trans.
  + apply comparelA_le_lt_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_eq_lt_trans.
- (* 1/3 *)
  intros [fa1 t1] [fa2 t2] [fa3 t3].
  apply compareAB_lt_le_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_lt_eq_trans.
  + apply comparelA_lt_le_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_lt_eq_trans.
- (* 1/2 *)
  intros [fa1 t1] [fa2 t2] [fa3 t3].
  apply compareAB_lt_trans.
  + apply Fset.compare_eq_trans.
  + apply Fset.compare_eq_lt_trans.
  + apply Fset.compare_lt_eq_trans.
  + apply Fset.compare_lt_trans.
  + apply comparelA_lt_trans.
    * do 6 intro; apply Oset.compare_eq_trans.
    * do 6 intro; apply Oset.compare_eq_lt_trans.
    * do 6 intro; apply Oset.compare_lt_eq_trans.
    * do 6 intro; apply Oset.compare_lt_trans.
- (* 1/1 *)
  intros [fa1 t1] [fa2 t2].
  apply compareAB_lt_gt.
  + apply Fset.compare_lt_gt.
  + apply comparelA_lt_gt.
    do 4 intro; apply Oset.compare_lt_gt.
Defined.

Definition FT : Feset.Rcd OTuple := Feset.build OTuple.
Definition BT : Febag.Rcd OTuple := Febag.build OTuple.
Definition CT := Fecol.mk_R FT BT.

Lemma tuple_eq_ok : 
  forall t1 t2, Oeset.compare OTuple t1 t2 = Eq <->
   support t1 =S= support t2 /\ (forall a, a inS support t1 -> dot t1 a = dot t2 a).
Proof.
intros [fa1 f1] [fa2 f2].
simpl support; simpl dot.
unfold Oeset.compare, FT, Feset.build, OTuple.
unfold tuple_compare.
unfold compareAB.
case_eq (Fset.compare FAN fa1 fa2); intro Hfa.
- rewrite <- Fset.compare_spec, Hfa.
  split.
  + intro Hf.
    split; [apply refl_equal | ].
    intros a Ha.
    rewrite Fset.compare_spec in Hfa.
    rewrite <- (Fset.elements_spec1 _ _ _ Hfa) in Hf.
    assert (Aux : map f1 ({{{fa1}}}) = map f2 ({{{fa1}}})).
    {
      assert (Aux := comparelA_eq_bool_ok (Oset.compare OVal)
                                        (map f1 ({{{fa1}}})) (map f2 ({{{fa1}}}))).
      rewrite Hf in Aux.
      apply Aux.
      intros; apply Oset.eq_bool_ok.
    } 
    rewrite <- map_eq in Aux.
    apply Aux.
    rewrite Fset.mem_elements, Oset.mem_bool_true_iff in Ha.
    apply Ha.
  + intros [_ Hf].
    rewrite Fset.compare_spec in Hfa.
    rewrite <- (Fset.elements_spec1 _ _ _ Hfa).
    replace (map f2 ({{{fa1}}})) with (map f1 ({{{fa1}}})).
    * apply comparelA_eq_refl.
      intros; apply Oset.compare_eq_refl.
    * rewrite <- map_eq.
      intros a Ha; apply Hf.
      rewrite Fset.mem_elements, Oset.mem_bool_true_iff; assumption.
- split; [intro Abs; discriminate Abs | ].
  intros [Abs _]; rewrite <- Fset.compare_spec in Abs.
  rewrite <- Hfa, <- Abs.
  apply refl_equal.
- split; [intro Abs; discriminate Abs | ].
  intros [Abs _]; rewrite <- Fset.compare_spec in Abs.
  rewrite <- Hfa, <- Abs.
  apply refl_equal.
Qed.

Definition T predicate symbol aggregate 
           (OP : Oset.Rcd predicate) 
           (OSymb : Oset.Rcd symbol)
           (OAgg : Oset.Rcd aggregate) 
           B interp_pred interp_symb interp_agg : Tuple.Rcd :=
(@Tuple.mk_R type attribute value predicate symbol aggregate tuple
             default_value _ FAN OVal FVal OP OSymb OAgg OTuple CT
             type_of_attribute type_of_value support dot mk_tuple 
             B interp_pred interp_symb interp_agg
             support_mk_tuple_ok dot_mk_tuple_ok tuple_eq_ok).

End Sec.

End Tuple1.

Module Tuple2.

Section Sec.

Hypothesis attribute : Type.
Hypothesis type : Type. 
Hypothesis value : Type.
Hypothesis type_of_attribute : attribute -> type. 
Hypothesis type_of_value : value -> type.
Hypothesis default_value : type -> value. 
Hypothesis OAtt : Oset.Rcd attribute. 
Hypothesis FAN : Fset.Rcd OAtt.
Hypothesis OT : Oset.Rcd type.
Hypothesis OVal : Oset.Rcd value.
Hypothesis FVal : Fset.Rcd OVal.

Definition tuple := (list (attribute * value)).

Definition support := fun (t : tuple) => Fset.mk_set FAN (map fst t).

Definition dot := fun (t : tuple) a => 
                    match Oset.find OAtt a t with
                    | Some v => v
                    | None => default_value (type_of_attribute a)
                    end.

Definition mk_tuple (fa : Fset.set FAN) (f : attribute -> value) : tuple := 
List.map (fun a => (a, f a)) (Fset.elements _ fa).

Lemma support_mk_tuple_ok : forall fa f, support (mk_tuple fa f) =S= fa.
Proof.
intros fa f; unfold mk_tuple; simpl; rewrite Fset.equal_spec; intros.
unfold support; rewrite Fset.mem_mk_set, map_map, map_id; [ | intros; apply refl_equal].
rewrite BasicFacts.eq_bool_iff, Oset.mem_bool_true_iff.
split; intro H.
- apply Fset.in_elements_mem; assumption.
- apply Fset.mem_in_elements; assumption.
Qed.

Lemma dot_mk_tuple_ok : 
  forall a s f, 
    dot (mk_tuple s f) a = (if a inS? s then f a else default_value (type_of_attribute a)).
Proof.
intros a fa f; unfold mk_tuple, dot; simpl.
case_eq (a inS? fa); intro Ha.
- rewrite Oset.find_map; trivial.
  apply Fset.mem_in_elements; assumption.
- case_eq (Oset.find OAtt a (map (fun a0 : attribute => (a0, f a0)) ({{{fa}}})));
    [ | intros; apply refl_equal].
  intros v Hv.
  assert (Abs := Oset.find_some _ _ _ Hv).
  rewrite in_map_iff in Abs.
  destruct Abs as [a' [Ha' Ka']].
  injection Ha'; clear Ha'; do 2 intro; subst a' v.
  rewrite (Fset.in_elements_mem _ _ _ Ka') in Ha; discriminate Ha.
Qed.

Definition tuple_compare (t1 t2 : tuple) : comparison :=
  comparelA (compareAB (Oset.compare OAtt) (Oset.compare OVal))
            (map (fun a => (a, dot t1 a)) (Fset.elements FAN (support t1)))
            (map (fun a => (a, dot t2 a)) (Fset.elements FAN (support t2))).

Definition OTuple : Oeset.Rcd tuple.
Proof.
split with tuple_compare; unfold tuple, tuple_compare.
- (* 1/5 *)
  do 3 intro; comparelA_tac; compareAB_tac; oset_compare_tac.
- (* 1/4 *)
  do 3 intro; comparelA_tac; compareAB_tac; oset_compare_tac.
- (* 1/3 *)
  do 3 intro; comparelA_tac; compareAB_tac; oset_compare_tac.
- (* 1/2 *)
  do 3 intro; comparelA_tac; compareAB_tac; oset_compare_tac.
- (* 1/1 *)
  do 2 intro; comparelA_tac; compareAB_tac; oset_compare_tac.
Defined.

Definition FT : Feset.Rcd OTuple := Feset.build OTuple.
Definition BT : Febag.Rcd OTuple := Febag.build OTuple.
Definition CT := Fecol.mk_R FT BT.

Lemma tuple_eq_ok : 
  forall t1 t2, Oeset.compare OTuple t1 t2 = Eq <->
   support t1 =S= support t2 /\ (forall a, a inS support t1 -> dot t1 a = dot t2 a).
Proof.
intros t1 t2; simpl.
unfold tuple_compare, support, dot; simpl; split.
- intro H; split.
  rewrite Fset.equal_spec; intro a.
  rewrite 2 Fset.mem_elements.
  set (l1 :=  ({{{Fset.mk_set FAN (map fst t1)}}})) in *.
  set (l2 :=  ({{{Fset.mk_set FAN (map fst t2)}}})) in *.
  clearbody l1 l2.
  revert l2 H; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
  + apply refl_equal.
  + simpl in H.
    case_eq (Oset.compare OAtt a1 a2); intro Ha; rewrite Ha in H; try discriminate H.
    rewrite Oset.compare_eq_iff in Ha; subst a2.
    case_eq (Oset.compare OVal
          match Oset.find OAtt a1 t1 with
          | Some v => v
          | None => default_value (type_of_attribute a1)
          end
          match Oset.find OAtt a1 t2 with
          | Some v => v
          | None => default_value (type_of_attribute a1)
          end); intro Hv; rewrite Hv in H; try discriminate H.
    simpl; apply f_equal.
    apply IHl1; trivial.
  + intros a Ha.
    set (f1 := fun a => 
                 (a, 
                  match Oset.find OAtt a t1 with 
                  | Some v => v
                  | None => default_value (type_of_attribute a)
                  end)) in *.
    set (f2 := fun a => 
                 (a, 
                  match Oset.find OAtt a t2 with 
                  | Some v => v
                  | None => default_value (type_of_attribute a)
                  end)) in *.
    change (match Oset.find OAtt a t1 with
            | Some v => v
            | None => default_value (type_of_attribute a)
            end) with (snd (f1 a)).
    change (match Oset.find OAtt a t2 with
            | Some v => v
            | None => default_value (type_of_attribute a)
            end) with (snd (f2 a)).
    apply f_equal.
    rewrite Fset.mem_elements, Oset.mem_bool_true_iff in Ha.
    set (l1 := ({{{Fset.mk_set FAN (map fst t1)}}})) in *.
    set (l2 := ({{{Fset.mk_set FAN (map fst t2)}}})) in *.
    clearbody l1 l2.
    revert l2 H; induction l1 as [ | a1 l1]; intros [ | a2 l2] H; try discriminate H.
    * contradiction Ha.
    * rewrite 2 (map_unfold _ (_ :: _)), comparelA_unfold in H.
      case_eq (compareAB (Oset.compare OAtt) (Oset.compare OVal) (f1 a1) (f2 a2)); 
        intro Hf; rewrite Hf in H; try discriminate H.
      {
        simpl in Ha; destruct Ha as [Ha | Ha].
        - subst a1.
          assert (Ha2 : a = a2).
          {
            unfold f1, f2 in Hf; simpl in Hf.
            case_eq (Oset.compare OAtt a a2); intro Ha2; rewrite Ha2 in Hf; try discriminate Hf.
            rewrite Oset.compare_eq_iff in Ha2; assumption.
          }
          subst a2.
          rewrite <- (Oset.compare_eq_iff (mk_opairs OAtt OVal)); apply Hf.
        - apply IHl1 with l2; trivial.
      }
- intros [H1 H2].
  rewrite <- (Fset.elements_spec1 _ _ _ H1).
  apply comparelA_eq_refl_alt.
  + intros [a d] Ha.
    apply compareAB_eq_refl; apply Oset.compare_eq_refl.
  + rewrite <- map_eq.
    intros a Ha; apply f_equal.
    apply H2; apply Fset.in_elements_mem; assumption.
Qed.

Definition T predicate symbol aggregate 
           (OP : Oset.Rcd predicate) 
           (OSymb : Oset.Rcd symbol)
           (OAgg : Oset.Rcd aggregate) 
           B interp_pred interp_symb interp_agg : Tuple.Rcd :=
(@Tuple.mk_R type attribute value predicate symbol aggregate tuple
             default_value _ FAN OVal FVal OP OSymb OAgg OTuple
             CT type_of_attribute type_of_value support dot mk_tuple 
             B interp_pred interp_symb interp_agg
             support_mk_tuple_ok dot_mk_tuple_ok tuple_eq_ok).

End Sec.

End Tuple2.

