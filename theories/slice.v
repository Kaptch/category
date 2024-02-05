From category Require Import base setoid category.

Section Slice.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Context {C : Category}.
  Context (c : C).

  Record SliceObj :=
    {
      slice_obj_src :> C;
      slice_obj_arr : Arr slice_obj_src c;
    }.

  Record SliceArr (A B : SliceObj) :=
    {
      slice_arr :> Arr A B;
      slice_arr_comp : slice_obj_arr B ∘ slice_arr ≡ slice_obj_arr A;
    }.

  Program Definition SliceArrSetoid (A B : SliceObj) : Setoid :=
    {|
      setoid_carrier := SliceArr A B;
      setoid_eq := @setoid_eq (Arr A B);
    |}.
  Next Obligation.
    intros.
    split.
    - intros ?.
      reflexivity.
    - intros ???.
      now symmetry.
    - intros ?? y ??.
      simpl in *.
      etransitivity; eassumption.
  Qed.

  Program Definition Slice : Category :=
    {|
      Obj := SliceObj;
      Arr A B := SliceArrSetoid A B;
      arrow_id A := {| slice_arr := ı |};
      arrow_comp A B C := λₛ f, λₛ g, {| slice_arr := f ∘ g |};
    |}.
  Next Obligation.
    intros.
    apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros.
    rewrite <-arrow_comp_assoc.
    rewrite slice_arr_comp.
    apply slice_arr_comp.
  Qed.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    apply arrow_comp_assoc.
  Qed.
End Slice.
