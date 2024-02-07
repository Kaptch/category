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
    now do 2 apply SetoidArrProper1.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    now apply SetoidArrProper1.
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

  Lemma Setoid_mono_inj {X Y : SetoidCat} (f : @Monomorphism SetoidCat X Y)
    : ∀ x y, monic f x ≡ monic f y → x ≡ y.
  Proof.
    intros x y H.
    pose proof (@monic_cancel SetoidCat X Y f).
    unshelve epose (Z := _ : SetoidCat).
    {
      unshelve refine {|
                   setoid_carrier := unit;
                 |}.
    }
    unshelve epose (x' := (λₛ i :: Z, x) : Z [~>] X).
    {
      intros; reflexivity.
    }
    unshelve epose (y' := (λₛ i :: Z, y) : Z [~>] X).
    {
      intros; reflexivity.
    }
    simpl in *.
    assert (f ∘ x' ≡ f ∘ y') as H1.
    {
      intros ?; simpl.
      unfold compose; assumption.
    }
    pose proof (@monic_cancel SetoidCat X Y f Z x' y' H1) as H2.
    specialize (H2 tt).
    simpl in H2.
    apply H2.
  Qed.
End Setoids.
