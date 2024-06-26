From category Require Import
  base
  setoid
  category.

Section Setoids.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Program Definition SetoidCat : Category :=
    {|
      Obj := Setoid;
      Arr A B := (A [→] B)%setoid;
      arrow_id A := {| setoid_arr := id |};
      arrow_comp _ _ _ := λₛ f, λₛ g, {| setoid_arr := compose f g |};
    |}.
  Next Obligation.
    intros; simpl.
    assumption.
  Qed.
  Next Obligation.
    intros; simpl.
    apply SetoidArrProper; [reflexivity | now apply SetoidArrProper].
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    apply SetoidArrProper; [reflexivity | now apply SetoidArrProper].
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
  Next Obligation.
    intros; simpl.
    now unfold compose.
  Qed.
End Setoids.
